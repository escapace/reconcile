import{workloads as prior}from'../v7/workloads.mjs';
import{equivalent as graphEquivalent}from'../v2/corpus.mjs';
import assert from'node:assert/strict';
export function equivalent(a,b){
 graphEquivalent(a,b);
 // The dedicated Temporal fixture is a flat dense array of all eight native types.
 if(Array.isArray(a))for(let i=0;i<a.length;i++)for(const name of['PlainMonthDay','PlainYearMonth']){
  const C=globalThis.Temporal?.[name];if(C&&a[i] instanceof C){
   const toString=C.prototype.toString;
   assert.equal(toString.call(a[i],{calendarName:'always'}),toString.call(b[i],{calendarName:'always'}),'Temporal hidden ISO reference date');
  }
 }
}
export const fixtures={
 'scalar-boundaries':()=>{const values=[undefined,NaN,Infinity,-Infinity,-0,0,-1,-2,-3,-4,-5,-6,-0.5,-1.5,-2.5,-3.5,-4.5,-5.5,-6.5,-7.25,-Number.MIN_VALUE,-Number.MAX_VALUE,-Number.MAX_SAFE_INTEGER,Number.MIN_VALUE,Number.MAX_VALUE,1,2,3,0.5,1.5,'-1','-0.5','NaN','Infinity','undefined','~0','~-1'];return Array.from({length:10000},(_,i)=>values[i%values.length])},
 'strings-10k':()=>Array.from({length:10000},(_,i)=>`item-${i}-alpha beta`),
 'numeric-10k':()=>Array.from({length:10000},(_,i)=>i*.25),
 'undefined-10k':()=>Array.from({length:10000},()=>undefined),
 'mixed-10k':()=>Array.from({length:10000},(_,i)=>[undefined,null,-0,NaN,Infinity,-Infinity,BigInt(i),`s${i}`,i][i%9]),
 'records-small':prior['json-small'],'records-1k':prior['json-1000'],'records-10k':prior['json-10000'],
 'dag-2k':prior['dag-2000'],'dense-dag':prior['dense-dag'],'cycle-300':prior['cycle-300'],
 'deep-200':prior['deep-200'],'deep-2000':()=>{let x={end:true};for(let i=0;i<2000;i++)x={next:x};return x},
 'collections':prior.collections,'dates-2k':prior['dates-2000'],'rich':prior.rich,
 'views-shared':()=>{const b=new ArrayBuffer(1024);new Uint8Array(b).set([1,2,3,4]);const v=new Uint8Array(b,8,40);return{b,v,alias:v,other:new DataView(b,16,20)}},
 'binary-1m':prior['binary-1m-entropy'],'url-linked':prior['URL-linked-100'],'temporal-exact':prior['Temporal-exact-200'],
 'hole-first':()=>{const a=Array.from({length:10000},(_,i)=>i);delete a[0];return a},
 'hole-last':()=>{const a=Array.from({length:10000},(_,i)=>i);delete a[9999];return a},
};
export const flags={
 'undefined-10k':'Dense own undefined elements; must not become holes.',
 'mixed-10k':'Object.is special numbers and bigint required.',
 'views-shared':'Backing-buffer identity, offsets, spans and distinct wrapper identities required.',
 'url-linked':'Owned URLSearchParams identity required; raw devalue may differ.',
 'temporal-exact':'All eight Temporal classes and exact hidden reference dates/components required.',
 'deep-2000':'Stack/resource boundary is recorded per codec, not silently excluded.',
 'hole-first':'Sparse success required: index0 absent, later own elements preserved.',
 'hole-last':'Sparse success required: final index absent and initial length preserved.',
};
