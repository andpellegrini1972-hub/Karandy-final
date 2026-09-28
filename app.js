(()=>{"use strict";
const $=s=>document.querySelector(s);
const ui={file:$("#file"),pick:$("#pick"),drop:$("#drop"),name:$("#fileName"),play:$("#play"),pause:$("#pause"),stop:$("#stop"),seek:$("#seek"),cur:$("#cur"),dur:$("#dur"),vol:$("#volume"),prev:$("#prev"),current:$("#current"),next:$("#next"),diag:$("#diag"),status:$("#status")};
let engineReady=false,sf2Buffer=null,midiBuffer=null,synth=null,audioCtx=null,audioNode=null,playing=false,startPerf=0,pausedSec=0,raf=null,lyrics=[],duration=0;
let dryGain=null,wetGain=null,convolver=null,compressor=null,chorusDelay=null,chorusOsc=null,masterGain=null;
const fmt=s=>{s=Math.max(0,s||0);return Math.floor(s/60)+":"+String(Math.floor(s%60)).padStart(2,"0")};
const read32=(d,i)=>((d[i]<<24)>>>0)+(d[i+1]<<16)+(d[i+2]<<8)+d[i+3];
const read16=(d,i)=>(d[i]<<8)+d[i+1];
const vlq=(d,p)=>{let v=0,b=0;do{b=d[p.i++];v=(v<<7)|(b&127)}while(b&128&&p.i<d.length);return v};
function decode(bytes){try{return new TextDecoder("windows-1252").decode(new Uint8Array(bytes))}catch(e){return String.fromCharCode(...bytes)}}
function parseLyrics(buf){
 const d=new Uint8Array(buf); if(String.fromCharCode(...d.slice(0,4))!=="MThd")throw Error("Header MIDI non valido");
 const format=read16(d,8),hlen=read32(d,4),tracks=read16(d,10),division=read16(d,12);let pos=8+hlen,tempos=[{tick:0,mpqn:500000}],rawLyrics=[],maxTick=0;
 const channels=new Set(),programs=new Set();let programChanges=0,controllers=0,pitchBends=0,sysex=0;
 for(let t=0;t<tracks;t++){if(String.fromCharCode(...d.slice(pos,pos+4))!=="MTrk")throw Error("Traccia MIDI non valida");const len=read32(d,pos+4),end=pos+8+len;let p={i:pos+8},tick=0,running=0;
  while(p.i<end){tick+=vlq(d,p);maxTick=Math.max(maxTick,tick);let st=d[p.i++];if(st<128){p.i--;st=running}else running=st;
   if(st===255){const type=d[p.i++],n=vlq(d,p),bytes=[...d.slice(p.i,p.i+n)];p.i+=n;if(type===81&&n===3)tempos.push({tick,mpqn:(bytes[0]<<16)+(bytes[1]<<8)+bytes[2]});else if(type===5||type===1)rawLyrics.push({tick,text:decode(bytes)});if(type===47)break}
   else if(st===240||st===247){const n=vlq(d,p);p.i+=n;sysex++}
   else{const hi=st&240,ch=st&15,n=(hi===192||hi===208)?1:2;channels.add(ch+1);if(hi===192){programChanges++;programs.add(d[p.i])}else if(hi===176)controllers++;else if(hi===224)pitchBends++;p.i+=n}
  }pos=end;
 }
 tempos.sort((a,b)=>a.tick-b.tick);const clean=[];for(const x of tempos){if(clean.length&&clean.at(-1).tick===x.tick)clean[clean.length-1]=x;else clean.push(x)}
 let acc=0,lastTick=0,lastMpqn=500000;for(const x of clean){acc+=(x.tick-lastTick)*lastMpqn/division/1e6;x.sec=acc;lastTick=x.tick;lastMpqn=x.mpqn}
 const toSec=t=>{let idx=0;for(let i=0;i<clean.length;i++){if(clean[i].tick<=t)idx=i;else break}const x=clean[idx];return x.sec+(t-x.tick)*x.mpqn/division/1e6};
 const ev=[],lines=[];let line="",li=0;
 for(const l of rawLyrics.sort((a,b)=>a.tick-b.tick)){let txt=l.text.replace(/\0/g,"");if(/^@/.test(txt.trim()))continue;for(const part of txt.split(/(\r\n|\r|\n)/)){if(!part)continue;if(/\r|\n/.test(part)){if(line.trim()){lines[li]=line.trim();li++;line=""}}else{line+=part;ev.push({sec:toSec(l.tick),lineIndex:li,text:line.trim()})}}}
 if(line.trim())lines[li]=line.trim();for(const e of ev){e.prev=lines[e.lineIndex-1]||"";e.next=lines[e.lineIndex+1]||""}
 return{lyrics:ev,duration:toSec(maxTick),tempoCount:clean.length,format,tracks,channels:[...channels],programCount:programs.size,programChanges,controllers,pitchBends,sysex};
}
function lyricAt(sec){if(!lyrics.length){ui.prev.textContent="";ui.current.textContent="Testo non presente";ui.next.textContent="";return}let b=-1;for(let i=0;i<lyrics.length;i++){if(lyrics[i].sec<=sec)b=i;else break}if(b<0){ui.current.textContent="♪";ui.prev.textContent="";ui.next.textContent=lyrics[0]?.next||"";return}const e=lyrics[b];ui.prev.textContent=e.prev;ui.current.textContent=e.text||"♪";ui.next.textContent=e.next}
function nowSec(){return playing?pausedSec+(performance.now()-startPerf)/1000:pausedSec}
function paint(){const t=Math.min(nowSec(),duration);ui.cur.textContent=fmt(t);ui.seek.value=duration?Math.round(t/duration*1000):0;lyricAt(t);if(playing&&t<duration+1)raf=requestAnimationFrame(paint)}
async function initEngine(){
 try{
  if(typeof JSSynth==="undefined")throw Error("Libreria FluidSynth non caricata");
  await JSSynth.waitForReady();
  ui.status.textContent="Caricamento GeneralUser GS ad alta qualità…";
  const r=await fetch("https://raw.githubusercontent.com/mrbumpy409/GeneralUser-GS/main/GeneralUser-GS.sf2");
  if(!r.ok)throw Error("GeneralUser GS non disponibile");
  sf2Buffer=await r.arrayBuffer();
  engineReady=true;
  ui.status.innerHTML='<span class="ok">FluidSynth + GeneralUser GS pronti. Carica un MIDI/KAR.</span>';
 }catch(e){ui.status.innerHTML='<span class="err">Errore motore: '+e.message+'</span>'}
}
async function createSynth(){
 if(synth){try{synth.close()}catch(e){}synth=null}
 if(chorusOsc){try{chorusOsc.stop()}catch(e){}chorusOsc=null}
 if(audioNode){try{audioNode.disconnect()}catch(e){}audioNode=null}
 if(audioCtx){try{await audioCtx.close()}catch(e){}audioCtx=null}
 audioCtx=new (window.AudioContext||window.webkitAudioContext)();
 if(audioCtx.state==="suspended")await audioCtx.resume();
 synth=new JSSynth.Synthesizer();synth.init(audioCtx.sampleRate);
 audioNode=synth.createAudioNode(audioCtx,8192);
 masterGain=audioCtx.createGain();masterGain.gain.value=.92;
 compressor=audioCtx.createDynamicsCompressor();
 compressor.threshold.value=-18;compressor.knee.value=18;compressor.ratio.value=2.2;compressor.attack.value=.01;compressor.release.value=.22;
 dryGain=audioCtx.createGain();dryGain.gain.value=.88;
 wetGain=audioCtx.createGain();wetGain.gain.value=.24;
 convolver=audioCtx.createConvolver();
 const irLen=Math.floor(audioCtx.sampleRate*1.65),ir=audioCtx.createBuffer(2,irLen,audioCtx.sampleRate);
 for(let c=0;c<2;c++){const data=ir.getChannelData(c);for(let i=0;i<irLen;i++){const decay=Math.pow(1-i/irLen,2.6);data[i]=(Math.random()*2-1)*decay*.42}}
 convolver.buffer=ir;
 chorusDelay=audioCtx.createDelay(.05);chorusDelay.delayTime.value=.018;
 chorusOsc=audioCtx.createOscillator();const chorusDepth=audioCtx.createGain();chorusDepth.gain.value=.0032;chorusOsc.frequency.value=.36;chorusOsc.connect(chorusDepth).connect(chorusDelay.delayTime);chorusOsc.start();
 const chorusGain=audioCtx.createGain();chorusGain.gain.value=.18;
 audioNode.connect(dryGain).connect(masterGain);
 audioNode.connect(convolver).connect(wetGain).connect(masterGain);
 audioNode.connect(chorusDelay).connect(chorusGain).connect(masterGain);
 masterGain.connect(compressor).connect(audioCtx.destination);
 await synth.loadSFont(sf2Buffer.slice(0));await synth.addSMFDataToPlayer(midiBuffer.slice(0));
 try{synth.setGain(.5)}catch(e){}
}
async function play(){
 if(!engineReady||!midiBuffer||playing)return;
 try{
  if(!synth){ui.status.textContent="Avvio FluidSynth…";await createSynth()}
  if(pausedSec>0){try{await synth.seekPlayer(Math.floor(pausedSec*1000))}catch(e){}}
  await synth.playPlayer();playing=true;startPerf=performance.now();buttons();paint();ui.status.innerHTML='<span class="ok">FluidSynth in riproduzione.</span>';
 }catch(e){playing=false;buttons();ui.status.innerHTML='<span class="err">Errore Play: '+e.message+'</span>';console.error(e)}
}
async function pause(){
 if(!playing)return;pausedSec=nowSec();playing=false;cancelAnimationFrame(raf);try{await synth.stopPlayer()}catch(e){}try{synth.close()}catch(e){}synth=null;buttons();ui.status.textContent="In pausa.";
}
async function stop(){
 playing=false;pausedSec=0;cancelAnimationFrame(raf);
 try{if(synth)await synth.stopPlayer()}catch(e){}
 try{if(synth)synth.close()}catch(e){}synth=null;
 if(chorusOsc){try{chorusOsc.stop()}catch(e){}chorusOsc=null}
 if(audioNode){try{audioNode.disconnect()}catch(e){}audioNode=null}
 if(audioCtx){try{await audioCtx.close()}catch(e){}audioCtx=null}
 ui.cur.textContent="0:00";ui.seek.value=0;lyricAt(0);buttons();ui.status.textContent="Stop.";
}
function buttons(){const ok=engineReady&&!!midiBuffer;ui.play.disabled=!ok||playing;ui.pause.disabled=!ok||!playing;ui.stop.disabled=!midiBuffer;ui.seek.disabled=!ok}
async function load(file){
 try{await stop();ui.status.textContent="Analisi MIDI…";midiBuffer=await file.arrayBuffer();const p=parseLyrics(midiBuffer);lyrics=p.lyrics;duration=p.duration;ui.name.textContent=file.name;ui.dur.textContent=fmt(duration);ui.diag.innerHTML=[
   ["FluidSynth","Engine"],["GeneralUser GS","SoundFont"],["Format "+p.format,p.tracks+" tracce"],[p.channels.length,p.channels.length===1?"Canale":"Canali"],[p.programCount,"Programmi"],[p.controllers,"Controller"],[p.pitchBends,"Pitch Bend"],[p.sysex,"SysEx"],[lyrics.length,"Lyrics"],[p.tempoCount,"Cambi tempo"]
  ].map(x=>'<div class="metric"><b>'+x[0]+'</b><span>'+x[1]+'</span></div>').join("");pausedSec=0;lyricAt(0);buttons();ui.status.innerHTML='<span class="ok">MIDI analizzato e pronto. Premi Play.</span>'}
 catch(e){midiBuffer=null;buttons();ui.status.innerHTML='<span class="err">'+e.message+'</span>'}
}
ui.pick.onclick=()=>ui.file.click();ui.file.onchange=e=>e.target.files[0]&&load(e.target.files[0]);ui.play.onclick=play;ui.pause.onclick=pause;ui.stop.onclick=stop;ui.vol.oninput=()=>{if(masterGain)masterGain.gain.value=Math.max(0,Math.min(1.4,+ui.vol.value));};ui.seek.oninput=()=>{if(!midiBuffer)return;const was=playing;if(was)pause();pausedSec=(+ui.seek.value/1000)*duration;ui.cur.textContent=fmt(pausedSec);lyricAt(pausedSec)};["dragenter","dragover"].forEach(ev=>ui.drop.addEventListener(ev,e=>{e.preventDefault()}));ui.drop.addEventListener("drop",e=>{e.preventDefault();e.dataTransfer.files[0]&&load(e.dataTransfer.files[0])});
let deferredInstall=null;
const installBtn=document.querySelector("#install");
window.addEventListener("beforeinstallprompt",e=>{e.preventDefault();deferredInstall=e;if(installBtn)installBtn.hidden=false});
if(installBtn)installBtn.onclick=async()=>{if(deferredInstall){deferredInstall.prompt();await deferredInstall.userChoice;deferredInstall=null;installBtn.hidden=true}else alert("Su iPhone: Condividi → Aggiungi alla schermata Home.")};
if("serviceWorker" in navigator)navigator.serviceWorker.register("/sw.js").catch(()=>{});
buttons();initEngine();
})();
