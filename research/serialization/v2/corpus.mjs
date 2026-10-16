import assert from 'node:assert/strict';
import {cases as previous,workloads as old,deep} from '../corpus.mjs';
export {deep};
const temporalNames=['Duration','Instant','PlainDate','PlainDateTime','PlainMonthDay','PlainTime','PlainYearMonth','ZonedDateTime'];
const fields=['years','months','weeks','days','hours','minutes','seconds','milliseconds','microseconds','nanoseconds'];
export function equivalent(a,b){const forward=new Map(),reverse=new Map(),pending=[[a,b]];while(pending.length){const[x,y]=pending.pop();if(x===null||typeof x!=='object'){assert(Object.is(x,y),`primitive mismatch ${String(x)} / ${String(y)}`);continue;}assert(y!==null&&typeof y==='object','object became primitive');if(forward.has(x)){assert.equal(forward.get(x),y,'shared identity split');continue;}assert(!reverse.has(y),'distinct identities merged');forward.set(x,y);reverse.set(y,x);assert.notEqual(x,y,'not detached');assert.equal(Object.getPrototypeOf(x),Object.getPrototypeOf(y),'prototype mismatch');
if(x instanceof URL){assert.equal(x.href,y.href,'URL href');pending.push([x.searchParams,y.searchParams]);continue;}
if(x instanceof URLSearchParams){assert.equal(x.toString(),y.toString(),'URL params');continue;}
const temporal=temporalNames.find(k=>globalThis.Temporal?.[k]&&x instanceof Temporal[k]);if(temporal){if(temporal==='Duration')for(const k of fields)assert.equal(x[k],y[k],`duration ${k}`);else assert(x.equals(y),'Temporal native equality');continue;}
if(x instanceof Date){assert(Object.is(+x,+y),'Date');continue;}
if(x instanceof ArrayBuffer){assert.deepEqual(new Uint8Array(x),new Uint8Array(y));continue;}
if(ArrayBuffer.isView(x)){assert.equal(x.byteOffset,y.byteOffset);assert.equal(x.byteLength,y.byteLength);pending.push([x.buffer,y.buffer]);continue;}
if(x instanceof Map){assert.equal(x.size,y.size);const yy=[...y];[...x].forEach(([k,v],i)=>pending.push([k,yy[i][0]],[v,yy[i][1]]));continue;}
if(x instanceof Set){assert.equal(x.size,y.size);const yy=[...y];[...x].forEach((v,i)=>pending.push([v,yy[i]]));continue;}
if(Array.isArray(x))assert.equal(x.length,y.length);const keys=Object.keys(x);assert.deepEqual(keys,Object.keys(y),'keys/order/holes');for(const k of keys)pending.push([x[k],y[k]]);
}}
export function temporalValues(){return [Temporal.Duration.from({seconds:1,milliseconds:1001,nanoseconds:3}),Temporal.Instant.from('2026-10-15T01:02:03.123456789Z'),Temporal.PlainDate.from('2026-10-15'),Temporal.PlainDateTime.from('2026-10-15T01:02:03.123456789'),new Temporal.PlainMonthDay(2,29,'iso8601',2000),Temporal.PlainTime.from('01:02:03.123456789'),new Temporal.PlainYearMonth(2026,10,'iso8601',15),Temporal.ZonedDateTime.from('2026-10-15T01:02:03+00:00[UTC]')];}
function linked(paramsFirst=true,n=1){return Array.from({length:n},(_,i)=>{const url=new URL(`https://example.test/path?x=${i}&x=two%20words`);return paramsFirst?{params:url.searchParams,url,again:url.searchParams}:{url,params:url.searchParams,again:url};});}
export const cases=[...previous,['URL-linked-params-first',()=>linked(true)[0]],['URL-linked-owner-first',()=>linked(false)[0]],['URL-equal-distinct',()=>[new URL('https://example.test'),new URL('https://example.test')]],['params-standalone',()=>new URLSearchParams('a=1&a=2&z=+')],['Temporal-all',()=>temporalValues()],['Temporal-aliases',()=>{const a=temporalValues();return {a,b:a.slice()};}],['deep-10000',()=>deep(10000)]];
export const workloads={...old,'numeric-array':()=>Array.from({length:10000},(_,i)=>i*.25),'string-array':()=>Array.from({length:5000},(_,i)=>'label-'+i),'collections':()=>{const keys=Array.from({length:500},(_,i)=>({i}));return {map:new Map(keys.map((k,i)=>[k,{i,key:k}])),set:new Set(keys)}},'bigint-array':()=>Array.from({length:1000},(_,i)=>BigInt(i)*1234567890123456789n),'Temporal-200':()=>Array.from({length:200},(_,i)=>Temporal.Instant.fromEpochNanoseconds(BigInt(i)*1000001n)),'URL-linked-100':()=>linked(true,100)};
workloads['deep-10000']=()=>deep(10000);
workloads['json-10000']=()=>Array.from({length:10000},(_,i)=>({id:i,name:`item-${i}`,active:i%2===0,values:[i,i+1,i+2]}));
