import assert from 'node:assert/strict';
// Independent graph bijection checks: not deepEqual (which can miss alias splits).
export function equivalent(a,b) {
 const forward=new Map(), reverse=new Map(), pending=[[a,b]];
 while(pending.length){const [x,y]=pending.pop();
  if(x===null || typeof x!=='object'){assert(Object.is(x,y),`primitive mismatch ${String(x)} / ${String(y)}`);continue;}
  assert(y!==null&&typeof y==='object','object became primitive');
  if(forward.has(x)){assert.equal(forward.get(x),y,'shared identity split');continue;}
  assert(!reverse.has(y),'distinct identities merged'); forward.set(x,y);reverse.set(y,x);assert.notEqual(x,y,'not detached');
  assert.equal(Object.getPrototypeOf(x),Object.getPrototypeOf(y),'prototype mismatch');
  if(x instanceof Date){assert(Object.is(+x,+y),'date mismatch');continue;}
  if(x instanceof ArrayBuffer){assert.deepEqual(new Uint8Array(x),new Uint8Array(y));continue;}
  if(ArrayBuffer.isView(x)){assert.equal(x.byteOffset,y.byteOffset);assert.equal(x.byteLength,y.byteLength);pending.push([x.buffer,y.buffer]);continue;}
  if(x instanceof Map){assert.equal(x.size,y.size);const yy=[...y];[...x].forEach(([k,v],i)=>pending.push([k,yy[i][0]],[v,yy[i][1]]));continue;}
  if(x instanceof Set){assert.equal(x.size,y.size);const yy=[...y];[...x].forEach((v,i)=>pending.push([v,yy[i]]));continue;}
  if(Array.isArray(x))assert.equal(x.length,y.length);
  const keys=Object.keys(x);assert.deepEqual(keys,Object.keys(y),'keys/order/holes mismatch');for(const k of keys)pending.push([x[k],y[k]]);
 }
}
const own=(o,k,v)=>Object.defineProperty(o,k,{value:v,writable:true,enumerable:true,configurable:true});
export const cases=[
 ['json',()=>({name:'Ada',enabled:true,count:3,items:[1,null,'x'],nested:{a:2}})],
 ['primitives',()=>[undefined,NaN,Infinity,-Infinity,-0,12n,null,true,'']],
 ['root-undefined',()=>undefined],['root-minuszero',()=>-0],['root-bigint',()=>99999999999999999999n],
 ['sparse',()=>{const x=new Array(7);x[2]=undefined;x[5]='v';return x;}],
 ['array-extra',()=>{const x=[1,,3];x.label='extra';return x;}],
 ['null-proto',()=>Object.assign(Object.create(null),{a:1})],
 ['collision-keys',()=>JSON.parse('{"__proto__":{"polluted":true},"constructor":{"prototype":{"x":1}},"$reconcile":1,"$ref":0,"meta":{"refs":[]},"data":null,"a.b":2,"a/b":3,"":4}')],
 ['dag',()=>{const a={n:1};return {a,b:a,c:{n:1}};}],
 ['cycle',()=>{const a={n:1};a.self=a;return a;}],
 ['collection-cycle',()=>{const k={},m=new Map(),s=new Set();m.set(k,s);s.add(m);return {k,m,s,again:m};}],
 ['self-collections',()=>{const m=new Map(),s=new Set();m.set(m,m);s.add(s);return {m,s};}],
 ['dates',()=>{const d=new Date(1234);return [d,d,new Date(NaN)];}],
 ['binary',()=>{const b=new ArrayBuffer(32);new Uint8Array(b).set([1,2,3,4]);const a=new Uint8Array(b,2,7);return {b,a,again:a,d:new DataView(b,3,5),other:new Uint16Array(b,4,3)};}],
 ['floatbits',()=>{const b=new ArrayBuffer(32),f=new Float64Array(b);f.set([NaN,-0,Infinity,-Infinity]);return {b,f};}],
 ['bigint-view',()=>new BigInt64Array([0n,-2n,999n])],
 ['distinct-buffers',()=>[new Uint8Array([1,2]),new Uint8Array([1,2])]],
 ['map-order',()=>new Map([[{},1],['z',2],[undefined,3],[NaN,4]])],
 ['deep-200',()=>deep(200)],
];
export function deep(n){let x={end:true};while(n--)x={next:x};return x;}
export const workloads={
 'json-small':()=>cases[0][1](),
 'json-1000':()=>Array.from({length:1000},(_,i)=>({id:i,name:`item-${i}`,active:i%2===0,values:[i,i+1,i+2]})),
 'rich':()=>({values:cases[1][1](),collections:cases[11][1](),dates:cases[13][1](),binary:cases[14][1]()}),
 'dag-2000':()=>{const pool=Array.from({length:20},(_,i)=>({id:i,label:`shared-${i}`}));return Array.from({length:2000},(_,i)=>({i,value:pool[i%20]}));},
 'cycle-300':()=>{const nodes=Array.from({length:300},(_,i)=>({i}));nodes.forEach((x,i)=>x.next=nodes[(i+1)%nodes.length]);return nodes;},
 'binary-64k':()=>{const b=new ArrayBuffer(65536);new Uint8Array(b).fill(42);return {b,a:new Uint8Array(b,8,4096),d:new DataView(b,32,8000)};},
 'deep-200':()=>deep(200),
};
