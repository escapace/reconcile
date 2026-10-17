import fs from'node:fs';import readline from'node:readline';import{performance}from'node:perf_hooks';import{createHash}from'node:crypto';import{gzipSync}from'node:zlib';import{fixtures,equivalent}from'./corpus.mjs';
const[name,scenario]=process.argv.slice(2),codec=await import(`./${name}-both.mjs`),value=fixtures[scenario](),text=codec.stringify(value);JSON.parse(text);equivalent(value,codec.parse(text));
const read=path=>{try{return fs.readFileSync(path,'utf8').trim()}catch{return null}},stat=()=>Object.fromEntries((read('/sys/fs/cgroup/cpu.stat')??'').split('\n').filter(Boolean).map(line=>{const[k,v]=line.split(/\s+/);return[k,Number(v)]}));
const host={node:process.version,base64:typeof Uint8Array.fromBase64==='function'?'native':'fallback',cpuMax:read('/sys/fs/cgroup/cpu.max'),memoryMax:read('/sys/fs/cgroup/memory.max'),memoryEventsBefore:read('/sys/fs/cgroup/memory.events'),affinity:read('/proc/self/status')?.split('\n').find(x=>x.startsWith('Cpus_allowed_list:'))};
let sink;const fns={encode:()=>codec.stringify(value),decode:()=>codec.parse(text),roundtrip:()=>codec.parse(codec.stringify(value))};
globalThis.gc?.();globalThis.gc?.();
console.log(JSON.stringify({ready:true,name,scenario,fidelity:'pass',host,payload:{bytes:Buffer.byteLength(text),gzip:gzipSync(text,{level:9}).length,sha256:createHash('sha256').update(text).digest('hex')}}));
for await(const line of readline.createInterface({input:process.stdin,crlfDelay:Infinity})){
 const request=JSON.parse(line);if(request.exit){console.log(JSON.stringify({done:true,memoryEventsAfter:read('/sys/fs/cgroup/memory.events'),throttleAfter:stat()}));process.exit(0)}
 const fn=fns[request.op],throttleBefore=stat(),cpuStart=process.cpuUsage(),start=performance.now();let calls=0;
 do{sink=fn();calls++}while(performance.now()-start<request.ms);
 const wallMs=performance.now()-start,cpu=process.cpuUsage(cpuStart),throttleAfter=stat();
 console.log(JSON.stringify({...request,name,calls,wallMs,usPerOp:wallMs*1000/calls,cpuUserUs:cpu.user,cpuSystemUs:cpu.system,cpuToWall:(cpu.user+cpu.system)/(wallMs*1000),throttleBefore,throttleAfter}));
}
