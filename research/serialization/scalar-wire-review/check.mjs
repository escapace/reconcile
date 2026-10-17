import assert from 'node:assert/strict';
import {pathToFileURL} from 'node:url';
const [path,mode]=process.argv.slice(2);
const {parse,stringify}=await import(pathToFileURL(path));
const offset=mode==='A'?6:1, specialOffset=mode==='A'?1:.5;
const ref=i=>-(i+offset), doc=(root,nodes=[],shapes=[])=>JSON.stringify([root,shapes,nodes]);
let checks=0;
function ok(test){assert(test);checks++}
function rejects(text){assert.throws(()=>parse(text),e=>e.cause?.type==='ParseInputInvalid',text);checks++}
const specials=[undefined,NaN,Infinity,-Infinity,-0];
for(let i=0;i<5;i++){
 const marker=-(i+specialOffset), value=specials[i];
 ok(Object.is(parse(doc(marker)),value));ok(JSON.parse(stringify(value))[0]===marker);
 ok(Object.is(parse(doc([-7,marker])),marker));ok(Object.is(parse(stringify(marker)),marker));
 ok(parse(stringify(String(marker)))===String(marker));
 rejects(doc([-(i+1)]));
}
for(const value of [null,true,false,'~u','-0','[-1]',0,1,Number.MAX_SAFE_INTEGER,Number.MAX_VALUE,Number.MIN_VALUE,-Number.MIN_VALUE,-Number.MAX_VALUE,17n,-17n])ok(Object.is(parse(stringify(value)),value));
const invalid=['-0','1e999','-1e999','[]','{}','[null]','[-0]','[1e999]','[-1e999]','["-1"]','[-1,0]','[-5,0]','[-6]','[-7]','[-7,-0]','[-7,0]','[-7,-1e999]','[-6,"00"]','[-6,"+1"]','[-6,1]','-9007199254740992'];
for(let n=-12;n<0;n+=.25)if(!specials.some((_,i)=>n===-(i+specialOffset)))invalid.push(String(n));
for(const raw of invalid){rejects(`[${raw},[],[]]`);if(raw!==String(ref(0)))rejects(`[${ref(0)},[],[[2,1,${raw}]]]`)}
let graph={};graph.self=graph;const distinct={};graph.a=distinct;graph.b=distinct;graph.c={};graph.values=[...specials,undefined];graph.sparse=new Array(5);graph.sparse[2]=undefined;graph.sparse[4]=graph;
const out=parse(stringify(graph));ok(out.self===out&&out.a===out.b&&out.a!==out.c);ok(out.sparse.length===5&&!Object.hasOwn(out.sparse,0)&&Object.hasOwn(out.sparse,2)&&out.sparse[4]===out);
for(let i=0;i<5;i++)ok(Object.is(out.values[i],specials[i]));
const buffer=new ArrayBuffer(12);new Uint8Array(buffer).set([1,2,3,4]);const a=new Uint8Array(buffer,2,4),b=new DataView(buffer,1,8);
const binary=parse(stringify({a,b,again:a,buffer}));ok(binary.a===binary.again&&binary.a.buffer===binary.buffer&&binary.b.buffer===binary.buffer);ok(binary.a.byteOffset===2&&binary.a.length===4&&binary.b.byteOffset===1&&binary.b.byteLength===8);binary.a[0]=99;ok(binary.b.getUint8(1)===99);
for(const order of [0,1]){const u=new URL('https://example.com/?a=1');const g=order?{u,p:u.searchParams}:{p:u.searchParams,u};const x=parse(stringify(g));ok(x.p===x.u.searchParams);x.p.set('b','2');ok(x.u.searchParams.get('b')==='2'&&x.u.href.includes('b=2'))}
for(const bad of [0,-0,.5,-.5,-1.5,ref(2),Number.MAX_SAFE_INTEGER,[-7,-1],...(mode==='A'?[-1,-2,-3,-4,-5]:[-2.5,-3.5,-4.5])])rejects(doc(ref(0),[[8,0,bad,0,0],[7,'']]));
for(const bad of [-1,1.5,Infinity,Number.MAX_SAFE_INTEGER])rejects(doc(ref(0),[[8,0,ref(1),bad,0],[7,'']]));
const polluted=parse(doc(ref(0),[[0,0,ref(1)],[0,1,true]],[['__proto__'],['polluted']]));ok(Object.hasOwn(polluted,'__proto__')&&Object.getPrototypeOf(polluted)===Object.prototype&&({}).polluted===undefined);
const trace=[];const child={get y(){trace.push('y');return undefined}};const source={get a(){trace.push('a');return child},get b(){trace.push('b');return child}};const observed=parse(stringify(source));ok(trace.join(',')==='a,y,b'&&observed.a===observed.b);
console.log(JSON.stringify({mode,checks,status:'PASS',path}));
