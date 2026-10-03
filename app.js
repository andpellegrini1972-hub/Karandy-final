(()=>{"use strict";
const SB_URL="https://iueptvoigqunotmjoner.supabase.co";
const SB_KEY="sb_publishable_ji1zyhS45qv1X6YGULRHyg_WAMKMDH8";
async function sbRpc(name,body){
 const r=await fetch(`${SB_URL}/rest/v1/rpc/${name}`,{
  method:"POST",
  headers:{"Content-Type":"application/json","apikey":SB_KEY,"Authorization":"Bearer "+SB_KEY},
  body:JSON.stringify(body||{})
 });
 if(!r.ok)throw Error((await r.text())||("Supabase "+r.status));
 return await r.json();
}
const $=s=>document.querySelector(s), $$=s=>[...document.querySelectorAll(s)];
const ui={file:$("#file"),pick:$("#pick"),drop:$("#drop"),name:$("#fileName"),play:$("#play"),pause:$("#pause"),stop:$("#stop"),seek:$("#seek"),cur:$("#cur"),dur:$("#dur"),vol:$("#volume"),tempo:$("#tempo"),prev:$("#prev"),current:$("#current"),next:$("#next"),diag:$("#diag"),status:$("#status"),video:$("#videoView"),audio:$("#audioElement"),engineDot:$("#engineDot"),singer:$("#singerBanner")};
const LS={prefs:"karandy_song_prefs_v1",queue:"karandy_queue_v1",mode:"karandy_event_mode_v1"};
let mode="none", currentFile=null, currentUrl=null, midiOriginal=null, midiBuffer=null, midiInfo=null;
let engineReady=false,sf2Buffer=null,synth=null,audioCtx=null,audioNode=null,masterGain=null,compressor=null,dryGain=null,wetGain=null,convolver=null,chorusDelay=null,chorusOsc=null;
let playing=false,startPerf=0,pausedSec=0,raf=null,duration=0,lyrics=[],externalLyrics=null;
let tone=0, tempoPct=100, displayWin=null, library=[], queue=JSON.parse(localStorage.getItem(LS.queue)||"[]");
let syncLines=[],syncTimes=[],syncIndex=0,syncing=false,lastMidiDiagram="";

const fmt=s=>{s=Math.max(0,s||0);return Math.floor(s/60)+":"+String(Math.floor(s%60)).padStart(2,"0")};
const toast=t=>{const e=$("#toast");e.textContent=t;e.classList.add("show");setTimeout(()=>e.classList.remove("show"),1800)};
function prefs(){return JSON.parse(localStorage.getItem(LS.prefs)||"{}")}
function savePrefsObj(o){localStorage.setItem(LS.prefs,JSON.stringify(o))}
function songKey(){return currentFile?currentFile.name.toLowerCase():""}
function applySavedPrefs(){
 const p=prefs()[songKey()]; if(!p)return;
 tone=p.tone??0;tempoPct=p.tempo??100;ui.vol.value=p.volume??.92;
 $("#toneValue").textContent=tone>0?`+${tone}`:tone;ui.tempo.value=tempoPct;$("#tempoValue").textContent=tempoPct+"%";$("#volValue").textContent=Math.round(ui.vol.value*100)+"%";
}
function saveCurrentPrefs(){
 if(!currentFile)return toast("Carica prima un brano");
 const all=prefs();all[songKey()]={tone,tempo:tempoPct,volume:+ui.vol.value};savePrefsObj(all);toast("Impostazioni brano salvate");
}

const read32=(d,i)=>((d[i]<<24)>>>0)+(d[i+1]<<16)+(d[i+2]<<8)+d[i+3], read16=(d,i)=>(d[i]<<8)+d[i+1];
const vlq=(d,p)=>{let v=0,b=0;do{b=d[p.i++];v=(v<<7)|(b&127)}while(b&128&&p.i<d.length);return v};
function decode(bytes){try{return new TextDecoder("windows-1252").decode(new Uint8Array(bytes))}catch(e){return String.fromCharCode(...bytes)}}
function parseMidi(buf){
 const d=new Uint8Array(buf);if(String.fromCharCode(...d.slice(0,4))!=="MThd")throw Error("Header MIDI non valido");
 const format=read16(d,8),hlen=read32(d,4),tracks=read16(d,10),division=read16(d,12);let pos=8+hlen,tempos=[{tick:0,mpqn:500000}],rawLyrics=[],maxTick=0,noteCount=0,zeroVel=0;
 const channels=new Set(),programs=new Set(),programByChannel={};let controllers=0,pitchBends=0,sysex=0;
 for(let t=0;t<tracks;t++){if(String.fromCharCode(...d.slice(pos,pos+4))!=="MTrk")throw Error("Traccia MIDI non valida");const len=read32(d,pos+4),end=pos+8+len;let p={i:pos+8},tick=0,running=0;
  while(p.i<end){tick+=vlq(d,p);maxTick=Math.max(maxTick,tick);let st=d[p.i++];if(st<128){p.i--;st=running}else running=st;
   if(st===255){const type=d[p.i++],n=vlq(d,p),bytes=[...d.slice(p.i,p.i+n)];p.i+=n;if(type===81&&n===3)tempos.push({tick,mpqn:(bytes[0]<<16)+(bytes[1]<<8)+bytes[2]});else if(type===5||type===1)rawLyrics.push({tick,text:decode(bytes)});if(type===47)break}
   else if(st===240||st===247){const n=vlq(d,p);p.i+=n;sysex++}
   else{const hi=st&240,ch=st&15,n=(hi===192||hi===208)?1:2;channels.add(ch+1);
    if(hi===192){programs.add(d[p.i]);programByChannel[ch+1]=d[p.i]}
    else if(hi===176)controllers++;else if(hi===224)pitchBends++;else if(hi===144){noteCount++;if(d[p.i+1]===0)zeroVel++}
    p.i+=n}
  }pos=end;
 }
 tempos.sort((a,b)=>a.tick-b.tick);const clean=[];for(const x of tempos){if(clean.length&&clean.at(-1).tick===x.tick)clean[clean.length-1]=x;else clean.push(x)}
 let acc=0,lastTick=0,lastMpqn=500000;for(const x of clean){acc+=(x.tick-lastTick)*lastMpqn/division/1e6;x.sec=acc;lastTick=x.tick;lastMpqn=x.mpqn}
 const toSec=t=>{let idx=0;for(let i=0;i<clean.length;i++){if(clean[i].tick<=t)idx=i;else break}const x=clean[idx];return x.sec+(t-x.tick)*x.mpqn/division/1e6};
 const ev=[],lines=[];let line="",li=0;
 for(const l of rawLyrics.sort((a,b)=>a.tick-b.tick)){let txt=l.text.replace(/\0/g,"");if(/^@/.test(txt.trim()))continue;for(const part of txt.split(/(\r\n|\r|\n)/)){if(!part)continue;if(/\r|\n/.test(part)){if(line.trim()){lines[li]=line.trim();li++;line=""}}else{line+=part;ev.push({sec:toSec(l.tick),lineIndex:li,text:line.trim()})}}}
 if(line.trim())lines[li]=line.trim();for(const e of ev){e.prev=lines[e.lineIndex-1]||"";e.next=lines[e.lineIndex+1]||""}
 return{lyrics:ev,duration:toSec(maxTick),tempoCount:clean.length,format,tracks,division,channels:[...channels],programCount:programs.size,programByChannel,controllers,pitchBends,sysex,noteCount,zeroVel};
}
function prepareMidi(buf,semi,tempo){
 const d=new Uint8Array(buf.slice(0));const hlen=read32(d,4),tracks=read16(d,10);let pos=8+hlen;
 for(let t=0;t<tracks;t++){const len=read32(d,pos+4),end=pos+8+len;let p={i:pos+8},running=0;
  while(p.i<end){vlq(d,p);let st=d[p.i++];if(st<128){p.i--;st=running}else running=st;
   if(st===255){const type=d[p.i++],n=vlq(d,p);if(type===81&&n===3&&tempo!==100){let mp=(d[p.i]<<16)+(d[p.i+1]<<8)+d[p.i+2];mp=Math.max(1,Math.round(mp/(tempo/100)));d[p.i]=(mp>>16)&255;d[p.i+1]=(mp>>8)&255;d[p.i+2]=mp&255}p.i+=n;if(type===47)break}
   else if(st===240||st===247){const n=vlq(d,p);p.i+=n}
   else{const hi=st&240,ch=st&15,n=(hi===192||hi===208)?1:2;
    if((hi===128||hi===144)&&ch!==9&&semi!==0){d[p.i]=Math.max(0,Math.min(127,d[p.i]+semi))}
    p.i+=n}
  }pos=end;
 }
 return d.buffer;
}
function scaleLyrics(base){const f=100/tempoPct;return base.map(x=>({...x,sec:x.sec*f}))}
function activeLyrics(){return externalLyrics||lyrics}
function lyricAt(sec){
 const arr=activeLyrics();if(!arr.length){ui.prev.textContent="";ui.current.textContent=mode==="video"?"Video karaoke":"Testo non disponibile";ui.next.textContent="";broadcastDisplay();return}
 let b=-1;for(let i=0;i<arr.length;i++){if(arr[i].sec<=sec)b=i;else break}
 if(b<0){ui.current.textContent="♪";ui.prev.textContent="";ui.next.textContent=arr[0]?.next||arr[0]?.text||""}
 else{const e=arr[b];ui.prev.textContent=e.prev||"";ui.current.textContent=e.text||"♪";ui.next.textContent=e.next||""}
 broadcastDisplay();
}

async function initEngine(){
 try{if(typeof JSSynth==="undefined")throw Error("Libreria FluidSynth non caricata");await JSSynth.waitForReady();ui.status.textContent="Caricamento GeneralUser GS…";
  const r=await fetch("https://raw.githubusercontent.com/mrbumpy409/GeneralUser-GS/main/GeneralUser-GS.sf2");if(!r.ok)throw Error("SoundFont non disponibile");
  sf2Buffer=await r.arrayBuffer();engineReady=true;ui.engineDot.classList.add("ready");ui.status.innerHTML='<span class="ok">Motore MIDI pronto.</span>';buttons()
 }catch(e){ui.status.innerHTML='<span class="err">Errore motore: '+e.message+'</span>'}
}
async function createSynth(){
 await destroySynth(false);
 audioCtx=new(window.AudioContext||window.webkitAudioContext)();if(audioCtx.state==="suspended")await audioCtx.resume();
 synth=new JSSynth.Synthesizer();synth.init(audioCtx.sampleRate);audioNode=synth.createAudioNode(audioCtx,8192);
 masterGain=audioCtx.createGain();masterGain.gain.value=+ui.vol.value;compressor=audioCtx.createDynamicsCompressor();compressor.threshold.value=-18;compressor.knee.value=18;compressor.ratio.value=2.2;compressor.attack.value=.01;compressor.release.value=.22;
 dryGain=audioCtx.createGain();dryGain.gain.value=.88;wetGain=audioCtx.createGain();wetGain.gain.value=.24;convolver=audioCtx.createConvolver();
 const irLen=Math.floor(audioCtx.sampleRate*1.65),ir=audioCtx.createBuffer(2,irLen,audioCtx.sampleRate);for(let c=0;c<2;c++){const data=ir.getChannelData(c);for(let i=0;i<irLen;i++){const decay=Math.pow(1-i/irLen,2.6);data[i]=(Math.random()*2-1)*decay*.42}}convolver.buffer=ir;
 chorusDelay=audioCtx.createDelay(.05);chorusDelay.delayTime.value=.018;chorusOsc=audioCtx.createOscillator();const depth=audioCtx.createGain();depth.gain.value=.0032;chorusOsc.frequency.value=.36;chorusOsc.connect(depth).connect(chorusDelay.delayTime);chorusOsc.start();const chorusGain=audioCtx.createGain();chorusGain.gain.value=.18;
 audioNode.connect(dryGain).connect(masterGain);audioNode.connect(convolver).connect(wetGain).connect(masterGain);audioNode.connect(chorusDelay).connect(chorusGain).connect(masterGain);masterGain.connect(compressor).connect(audioCtx.destination);
 midiBuffer=prepareMidi(midiOriginal,tone,tempoPct);await synth.loadSFont(sf2Buffer.slice(0));await synth.addSMFDataToPlayer(midiBuffer.slice(0));try{synth.setGain(.5)}catch(e){}
}
async function destroySynth(stop=true){
 try{if(synth&&stop)await synth.stopPlayer()}catch(e){}
 if(chorusOsc){try{chorusOsc.stop()}catch(e){}chorusOsc=null}if(audioNode){try{audioNode.disconnect()}catch(e){}audioNode=null}if(audioCtx){try{await audioCtx.close()}catch(e){}audioCtx=null}if(synth){try{synth.close()}catch(e){}synth=null}
 masterGain=compressor=dryGain=wetGain=convolver=chorusDelay=null;
}
function mediaEl(){return mode==="video"?ui.video:ui.audio}
function nowSec(){if(mode==="midi")return playing?pausedSec+(performance.now()-startPerf)/1000:pausedSec;const m=mediaEl();return m?.currentTime||0}
function paint(){const t=Math.min(nowSec(),duration||1e9);ui.cur.textContent=fmt(t);ui.seek.value=duration?Math.round(t/duration*1000):0;lyricAt(t);if(playing)raf=requestAnimationFrame(paint)}
async function play(){
 if(!currentFile||playing)return;
 try{
  if(mode==="midi"){if(!engineReady)return toast("Motore MIDI non pronto");if(!synth){await createSynth();await synth.playPlayer()}else if(audioCtx&&audioCtx.state==="suspended")await audioCtx.resume();playing=true;startPerf=performance.now()}
  else{const m=mediaEl();m.volume=Math.min(1,+ui.vol.value);m.playbackRate=tempoPct/100;try{m.preservesPitch=true;m.webkitPreservesPitch=true}catch(e){};await m.play();playing=true}
  buttons();paint();ui.status.innerHTML='<span class="ok">Riproduzione attiva.</span>'
 }catch(e){playing=false;buttons();ui.status.innerHTML='<span class="err">Errore Play: '+e.message+'</span>'}
}
async function pause(){
 if(!playing)return;pausedSec=nowSec();playing=false;cancelAnimationFrame(raf);
 if(mode==="midi"){if(audioCtx&&audioCtx.state==="running")await audioCtx.suspend()}else mediaEl().pause();
 buttons();ui.status.textContent="In pausa."
}
async function stop(){
 playing=false;pausedSec=0;cancelAnimationFrame(raf);
 if(mode==="midi")await destroySynth(true);else{const m=mediaEl();m.pause();try{m.currentTime=0}catch(e){}}
 ui.cur.textContent="0:00";ui.seek.value=0;lyricAt(0);buttons();ui.status.textContent="Stop."
}
function buttons(){const ok=!!currentFile && (mode!=="midi"||engineReady);ui.play.disabled=!ok||playing;ui.pause.disabled=!ok||!playing;ui.stop.disabled=!currentFile;ui.seek.disabled=!ok}
async function loadFile(file){
 await stop();externalLyrics=null;currentFile=file;ui.name.textContent=file.name;applySavedPrefs();
 const ext=(file.name.split(".").pop()||"").toLowerCase();mode=["mid","midi","kar"].includes(ext)?"midi":["mp4","mov","m4v","webm"].includes(ext)||file.type.startsWith("video")?"video":"audio";
 $("#engineLabel").textContent=mode==="midi"?"GM / GS":mode.toUpperCase();ui.video.hidden=mode!=="video";
 if(currentUrl)URL.revokeObjectURL(currentUrl);currentUrl=URL.createObjectURL(file);
 if(mode==="midi"){midiOriginal=await file.arrayBuffer();midiInfo=parseMidi(midiOriginal);duration=midiInfo.duration*(100/tempoPct);lyrics=scaleLyrics(midiInfo.lyrics);renderMidiInfo();ui.dur.textContent=fmt(duration);lyricAt(0);ui.status.innerHTML='<span class="ok">MIDI pronto. Premi Play.</span>'}
 else{const m=mediaEl();m.src=currentUrl;m.load();await new Promise(res=>{m.onloadedmetadata=()=>res();setTimeout(res,1200)});duration=Number.isFinite(m.duration)?m.duration:0;lyrics=[];ui.dur.textContent=fmt(duration);ui.diag.innerHTML='<div class="metric"><b>'+mode.toUpperCase()+'</b><span>Media locale</span></div>';ui.status.innerHTML='<span class="ok">Brano pronto.</span>';lyricAt(0)}
 buttons();broadcastDisplay()
}
function renderMidiInfo(){
 const p=midiInfo;ui.diag.innerHTML=[["FluidSynth","Engine"],["GeneralUser GS","SoundFont"],["Format "+p.format,p.tracks+" tracce"],[p.channels.length,"Canali"],[p.programCount,"Programmi"],[p.controllers,"Controller"],[p.pitchBends,"Pitch Bend"],[p.sysex,"SysEx"],[p.lyrics.length,"Lyrics"],[p.tempoCount,"Cambi tempo"]].map(x=>'<div class="metric"><b>'+x[0]+'</b><span>'+x[1]+'</span></div>').join("");
 lastMidiDiagram=`FORMAT ${p.format}\nTRACCE ${p.tracks}\nPPQN ${p.division}\nCANALI ${p.channels.join(", ")}\nNOTE ${p.noteCount}\nPROGRAMMI ${p.programCount}\nCONTROLLER ${p.controllers}\nPITCH BEND ${p.pitchBends}\nSYSEX ${p.sysex}\nLYRICS ${p.lyrics.length}\nCAMBI TEMPO ${p.tempoCount}\n\nPROGRAM CHANGE PER CANALE\n${Object.entries(p.programByChannel).map(([c,v])=>`CH ${c}: program ${v}`).join("\n")||"Nessuno"}`;
 $("#midiDiagram").textContent=lastMidiDiagram
}
async function changeMidiSettings(){
 $("#toneValue").textContent=tone>0?`+${tone}`:tone;$("#tempoValue").textContent=tempoPct+"%";
 if(mode==="midi"&&midiInfo){duration=midiInfo.duration*(100/tempoPct);lyrics=scaleLyrics(midiInfo.lyrics);ui.dur.textContent=fmt(duration);if(playing||synth){await stop();toast("Impostazione applicata. Premi Play")}}
 else if(currentFile&&mode!=="midi"){const m=mediaEl();m.playbackRate=tempoPct/100}
}
function parseLrc(txt){
 const out=[];for(const line of txt.split(/\r?\n/)){const matches=[...line.matchAll(/\[(\d{1,2}):(\d{2}(?:\.\d+)?)\]/g)];const text=line.replace(/\[[^\]]+\]/g,"").trim();for(const m of matches)out.push({sec:+m[1]*60+parseFloat(m[2]),text})}
 out.sort((a,b)=>a.sec-b.sec);for(let i=0;i<out.length;i++){out[i].prev=out[i-1]?.text||"";out[i].next=out[i+1]?.text||""}return out
}
function formatLrcTime(sec){const m=Math.floor(sec/60),s=sec-m*60;return`[${String(m).padStart(2,"0")}:${s.toFixed(2).padStart(5,"0")}]`}
function renderLyricsPreview(arr){$("#lyricsPreview").value=arr.map(x=>`${formatLrcTime(x.sec)}${x.text}`).join("\n")}
function libraryAdd(files){for(const f of files){if(!library.some(x=>x.name===f.name&&x.size===f.size))library.push(f)}renderLibrary()}
function renderLibrary(){
 const q=$("#songSearch").value.toLowerCase(),list=library.filter(f=>f.name.toLowerCase().includes(q));const el=$("#songList");
 if(!list.length){el.className="list empty";el.textContent="Nessun brano trovato";return}el.className="list";el.innerHTML="";
 list.forEach(f=>{const d=document.createElement("div");d.className="list-item";d.innerHTML=`<div><strong>${esc(f.name)}</strong><small>${(f.size/1048576).toFixed(1)} MB</small></div><div class="item-actions"><button data-open>Apri</button><button data-queue>＋</button></div>`;d.querySelector("[data-open]").onclick=()=>{loadFile(f);closePanels()};d.querySelector("[data-queue]").onclick=()=>addQueueFromFile(f);el.appendChild(d)})
}
function addQueueFromFile(f){queue.push({id:crypto.randomUUID?.()||Date.now()+Math.random(),fileName:f.name,singer:$("#singerName").value||"",type:$("#performanceType").value||"Solista",dedication:$("#dedication").value||"",tone:0,status:"Pronto"});persistQueue()}
function addCurrentQueue(){if(!currentFile)return toast("Carica prima un brano");queue.push({id:crypto.randomUUID?.()||Date.now(),fileName:currentFile.name,singer:$("#singerName").value||"",type:$("#performanceType").value,dedication:$("#dedication").value||"",tone,status:"Pronto"});persistQueue();toast("Aggiunto alla scaletta")}
function persistQueue(){localStorage.setItem(LS.queue,JSON.stringify(queue));renderQueue();$("#queueBadge").textContent=queue.length}
function renderQueue(){
 const el=$("#queueList");if(!queue.length){el.className="list empty";el.textContent="Scaletta vuota";return}el.className="list";el.innerHTML="";
 queue.forEach((q,i)=>{const d=document.createElement("div");d.className="list-item";d.innerHTML=`<div><strong>${i+1}. ${esc(q.singer||"Cantante")} · ${esc(q.fileName)}</strong><small>${esc(q.type)} · tono ${q.tone>0?"+":""}${q.tone}${q.dedication?" · "+esc(q.dedication):""}</small></div><div class="item-actions"><button data-up>↑</button><button data-down>↓</button><button data-del>×</button></div>`;d.querySelector("[data-up]").onclick=()=>{if(i){[queue[i-1],queue[i]]=[queue[i],queue[i-1]];persistQueue()}};d.querySelector("[data-down]").onclick=()=>{if(i<queue.length-1){[queue[i+1],queue[i]]=[queue[i],queue[i+1]];persistQueue()}};d.querySelector("[data-del]").onclick=()=>{queue.splice(i,1);persistQueue()};el.appendChild(d)})
}
function esc(s){return String(s??"").replace(/[&<>"']/g,m=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#039;"}[m]))}
function openPanel(id){closePanels();$("#"+id)?.classList.add("open")}
function closePanels(){$$(".panel").forEach(p=>p.classList.remove("open"))}
function startEditor(){
 syncLines=$("#editorText").value.split(/\r?\n/).map(x=>x.trim()).filter(Boolean);syncTimes=[];syncIndex=0;syncing=syncLines.length>0;$("#syncTotal").textContent=syncLines.length;$("#syncIndex").textContent=syncIndex;$("#markLine").disabled=!syncing;updateSyncLine();if(syncing)toast("Avvia il brano e marca ogni riga")
}
function updateSyncLine(){$("#syncCurrentLine").textContent=syncLines[syncIndex]||"Sincronizzazione completata";$("#syncIndex").textContent=Math.min(syncIndex+1,syncLines.length)}
function markLine(){if(!syncing||syncIndex>=syncLines.length)return;syncTimes[syncIndex]=nowSec();syncIndex++;updateSyncLine();if(syncIndex>=syncLines.length){syncing=false;$("#markLine").disabled=true;toast("Sincronizzazione completata")}}
function exportLrc(){
 if(!syncLines.length||!syncTimes.length)return toast("Sincronizza prima il testo");const txt=syncLines.map((l,i)=>`${formatLrcTime(syncTimes[i]??0)}${l}`).join("\n");const a=document.createElement("a");a.href=URL.createObjectURL(new Blob([txt],{type:"text/plain"}));a.download=(currentFile?.name.replace(/\.[^.]+$/,"")||"KarAndy")+".lrc";a.click();setTimeout(()=>URL.revokeObjectURL(a.href),1000)
}
function openDisplay(){
 if(displayWin&&!displayWin.closed){displayWin.focus();return}
 displayWin=window.open("","KarAndyDisplay","popup,width=1000,height=700");if(!displayWin)return toast("Consenti le finestre popup");
 displayWin.document.write(`<!doctype html><html><head><title>KarAndy Display</title><style>html,body{margin:0;background:#000;color:#fff;height:100%;font-family:-apple-system,sans-serif}body{display:grid;place-items:center}.wrap{text-align:center;width:94%}.s{color:#55dfff;font-size:3vw;font-weight:800}.p,.n{color:#777;font-size:3.2vw;min-height:1.5em}.c{font-size:6vw;font-weight:1000;line-height:1.05;background:linear-gradient(90deg,#ff30db,#fff,#39dfff);-webkit-background-clip:text;color:transparent}</style></head><body><div class="wrap"><div class="s" id="s"></div><div class="p" id="p"></div><div class="c" id="c">KarAndy</div><div class="n" id="n"></div></div></body></html>`);displayWin.document.close();broadcastDisplay()
}
function broadcastDisplay(){if(!displayWin||displayWin.closed)return;try{displayWin.document.getElementById("s").textContent=ui.singer.textContent;displayWin.document.getElementById("p").textContent=ui.prev.textContent;displayWin.document.getElementById("c").textContent=ui.current.textContent;displayWin.document.getElementById("n").textContent=ui.next.textContent}catch(e){}}
async function createQr(){
 try{
  const venue=$("#venueName").value.trim()||"KarAndy";
  const type=$("#eventType").value;
  let operatorToken=localStorage.getItem("karandy_operator_token");
  if(!operatorToken){operatorToken=(crypto.randomUUID?.()||Math.random().toString(36).slice(2)+Date.now());localStorage.setItem("karandy_operator_token",operatorToken)}
  $("#generateQr").disabled=true;$("#generateQr").textContent="Creazione…";
  const code=await sbRpc("karandy_create_event",{p_venue:venue,p_event_type:type,p_operator_token:operatorToken});
  const eventCode=String(code).replace(/"/g,"").trim();
  const url=location.origin+location.pathname+"?event="+encodeURIComponent(eventCode);
  const box=$("#qrBox");box.innerHTML="";
  if(window.QRCode?.toCanvas){const c=document.createElement("canvas");box.appendChild(c);QRCode.toCanvas(c,url,{width:210,margin:1},()=>{})}else box.innerHTML=`<a href="${url}" target="_blank">${url}</a>`;
  localStorage.setItem("karandy_event",JSON.stringify({code:eventCode,venue,type,url,operatorToken}));
  toast("Sessione "+eventCode+" attiva");
  startRequestPolling();
 }catch(e){toast("Errore QR: "+e.message)}
 finally{$("#generateQr").disabled=false;$("#generateQr").textContent="Genera sessione"}
}
let requestPollTimer=null;
async function refreshRequests(){
 const ev=JSON.parse(localStorage.getItem("karandy_event")||"null");if(!ev?.code||!ev?.operatorToken)return;
 try{
  const rows=await sbRpc("karandy_get_requests",{p_event_code:ev.code,p_operator_token:ev.operatorToken});
  const el=$("#requestList");if(!rows.length){el.className="list empty";el.textContent="Nessuna richiesta ricevuta";return}
  el.className="list";el.innerHTML="";
  rows.forEach(r=>{const d=document.createElement("div");d.className="list-item";d.innerHTML=`<div><strong>${esc(r.singer)} · ${esc(r.song)}</strong><small>${esc(r.performance)} · tono ${r.tone>0?"+":""}${r.tone}${r.dedication?" · "+esc(r.dedication):""} · ${esc(r.status)}</small></div><div class="item-actions"><button data-add>＋ Scaletta</button><button data-done>✓</button></div>`;d.querySelector("[data-add]").onclick=()=>{queue.push({id:"req-"+r.id,fileName:r.song,singer:r.singer,type:r.performance,dedication:r.dedication||"",tone:r.tone,status:"Da associare"});persistQueue();toast("Richiesta aggiunta alla scaletta")};d.querySelector("[data-done]").onclick=async()=>{await sbRpc("karandy_update_request_status",{p_id:r.id,p_event_code:ev.code,p_operator_token:ev.operatorToken,p_status:"Eseguita"});refreshRequests()};el.appendChild(d)})
 }catch(e){console.warn("QR poll",e)}
}
function startRequestPolling(){clearInterval(requestPollTimer);refreshRequests();requestPollTimer=setInterval(refreshRequests,4000)}
function setEventMode(v){localStorage.setItem(LS.mode,v);$("#currentEventMode").textContent=v;toast("Modalità "+v)}
function handlePublicRequestMode(){
 const code=new URLSearchParams(location.search).get("event");if(!code)return false;
 document.body.innerHTML=`<main style="max-width:560px;margin:24px auto;padding:20px;font-family:-apple-system,sans-serif;color:white"><div style="background:#16051f;border:1px solid #50205d;border-radius:22px;padding:22px"><h1 style="margin-top:0">KarAndy</h1><h2>Richiedi il tuo brano</h2><p style="color:#b49dbe">Sessione <b>${esc(code)}</b></p><input id="rname" placeholder="Nome / soprannome" style="width:100%;padding:13px;margin:6px 0;border-radius:10px;border:1px solid #61306d;background:#0b0610;color:white"><input id="rsong" placeholder="Titolo / artista" style="width:100%;padding:13px;margin:6px 0;border-radius:10px;border:1px solid #61306d;background:#0b0610;color:white"><div style="display:grid;grid-template-columns:1fr 1fr;gap:8px"><select id="rtype" style="padding:13px;border-radius:10px;background:#0b0610;color:white"><option>Solista</option><option>Duetto</option></select><select id="rtone" style="padding:13px;border-radius:10px;background:#0b0610;color:white">${Array.from({length:13},(_,i)=>i-6).map(v=>`<option value="${v}">Tono ${v>0?"+":""}${v}</option>`).join("")}</select></div><textarea id="rded" placeholder="Dedica (facoltativa)" style="width:100%;padding:13px;margin:8px 0;border-radius:10px;border:1px solid #61306d;background:#0b0610;color:white"></textarea><button id="rsend" style="width:100%;padding:14px;border:0;border-radius:12px;background:linear-gradient(90deg,#c719ff,#fa2aca);color:white;font-weight:900">INVIA RICHIESTA</button><div id="rmsg" style="margin-top:12px;color:#62f0a0"></div></div></main>`;
 document.body.style.background="linear-gradient(180deg,#120018,#07000b)";
 $("#rsend").onclick=async()=>{const singer=$("#rname").value.trim(),song=$("#rsong").value.trim();if(!singer||!song){$("#rmsg").textContent="Inserisci nome e brano.";return}$("#rsend").disabled=true;$("#rsend").textContent="Invio…";try{await sbRpc("karandy_submit_request",{p_event_code:code,p_singer:singer,p_song:song,p_tone:+$("#rtone").value,p_performance:$("#rtype").value,p_dedication:$("#rded").value.trim()});$("#rmsg").textContent="Richiesta inviata! Ti aspettiamo in scaletta.";$("#rsong").value="";$("#rded").value=""}catch(e){$("#rmsg").textContent="Errore: "+e.message}finally{$("#rsend").disabled=false;$("#rsend").textContent="INVIA RICHIESTA"}};
 return true
}

ui.pick.onclick=()=>ui.file.click();$("#logoOpen").onclick=()=>ui.file.click();ui.file.onchange=e=>e.target.files[0]&&loadFile(e.target.files[0]);
["dragenter","dragover"].forEach(ev=>ui.drop.addEventListener(ev,e=>e.preventDefault()));ui.drop.addEventListener("drop",e=>{e.preventDefault();e.dataTransfer.files[0]&&loadFile(e.dataTransfer.files[0])});
ui.play.onclick=play;ui.pause.onclick=pause;ui.stop.onclick=stop;
ui.vol.oninput=()=>{$("#volValue").textContent=Math.round(ui.vol.value*100)+"%";if(masterGain)masterGain.gain.value=+ui.vol.value;if(mode!=="midi"&&currentFile)mediaEl().volume=Math.min(1,+ui.vol.value)};
ui.tempo.oninput=()=>{tempoPct=+ui.tempo.value;$("#tempoValue").textContent=tempoPct+"%"};ui.tempo.onchange=changeMidiSettings;
$("#toneDown").onclick=()=>{tone=Math.max(-6,tone-1);changeMidiSettings()};$("#toneUp").onclick=()=>{tone=Math.min(6,tone+1);changeMidiSettings()};
ui.seek.onchange=async()=>{if(!currentFile)return;const target=(+ui.seek.value/1000)*duration;if(mode==="midi"){toast("Seek MIDI verrà perfezionato nella prossima revisione");ui.seek.value=duration?Math.round(nowSec()/duration*1000):0}else{mediaEl().currentTime=target;lyricAt(target)}};
$("#saveBtn").onclick=saveCurrentPrefs;$("#displayBtn").onclick=openDisplay;
$$(".dock [data-panel]").forEach(b=>b.onclick=()=>openPanel(b.dataset.panel));$$(".panel .close").forEach(b=>b.onclick=closePanels);
$("#addSongsBtn").onclick=()=>$("#songsInput").click();$("#songsInput").onchange=e=>libraryAdd([...e.target.files]);$("#openFolderBtn").onclick=()=>$("#folderInput").click();$("#folderInput").onchange=e=>libraryAdd([...e.target.files]);$("#songSearch").oninput=renderLibrary;
$("#addCurrentQueue").onclick=addCurrentQueue;$("#clearQueue").onclick=()=>{if(confirm("Svuotare la scaletta?")){queue=[];persistQueue()}};$("#saveQueue").onclick=()=>{localStorage.setItem(LS.queue,JSON.stringify(queue));toast("Scaletta salvata")};
$("#loadLrcBtn").onclick=()=>$("#lrcInput").click();$("#lrcInput").onchange=async e=>{const f=e.target.files[0];if(!f)return;externalLyrics=parseLrc(await f.text());renderLyricsPreview(externalLyrics);lyricAt(nowSec());toast(externalLyrics.length+" righe LRC caricate")};$("#clearLyrics").onclick=()=>{externalLyrics=null;$("#lyricsPreview").value="";lyricAt(nowSec())};
$("#startSync").onclick=startEditor;$("#markLine").onclick=markLine;$("#backLine").onclick=()=>{if(syncIndex>0){syncIndex--;syncTimes.length=syncIndex;syncing=true;$("#markLine").disabled=false;updateSyncLine()}};$("#exportLrc").onclick=exportLrc;
$("#qrTopBtn").onclick=()=>{openPanel("qrPanel");const ev=JSON.parse(localStorage.getItem("karandy_event")||"null");if(ev?.code){const box=$("#qrBox");box.innerHTML="";if(window.QRCode?.toCanvas){const c=document.createElement("canvas");box.appendChild(c);QRCode.toCanvas(c,ev.url,{width:210,margin:1},()=>{})}startRequestPolling()}};$("#generateQr").onclick=createQr;$("#eventModeBtn").onclick=()=>openPanel("eventPanel");$$("[data-event]").forEach(b=>b.onclick=()=>setEventMode(b.dataset.event));
$("#manualBtn").onclick=()=>toast("Manuale integrato: usa Brani, Scaletta, Testo, Editor e Display");
let deferredInstall=null;const installBtn=$("#install");window.addEventListener("beforeinstallprompt",e=>{e.preventDefault();deferredInstall=e;installBtn.hidden=false});installBtn.onclick=async()=>{if(deferredInstall){deferredInstall.prompt();await deferredInstall.userChoice;deferredInstall=null;installBtn.hidden=true}else alert("Su iPhone: Safari → Condividi → Aggiungi alla schermata Home.")};
if("serviceWorker"in navigator)navigator.serviceWorker.register("/sw.js").catch(()=>{});
if(handlePublicRequestMode())return;
$("#currentEventMode").textContent=localStorage.getItem(LS.mode)||"Locale";persistQueue();buttons();initEngine();
})();