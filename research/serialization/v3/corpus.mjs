import {cases as old,workloads as existing} from '../v2/corpus.mjs';
export {equivalent} from '../v2/corpus.mjs';
function binary(size){const storage=new ArrayBuffer(size);let seed=123456789;const b=new Uint8Array(storage);for(let i=0;i<size;i++){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;b[i]=seed&255}return {storage,a:new Uint8Array(storage,8,size-16),b:new DataView(storage,4,size-8)}}
export const workloads={...existing,'binary-64k-entropy':()=>binary(65536),'binary-1m-entropy':()=>binary(1048576)};
export const cases=[...old,['equal-distinct-buffers',()=>{const a=new Uint8Array([1,2,3]).buffer,b=a.slice(0);return {a,b,av:new Uint8Array(a),bv:new DataView(b)}}],['unicode-reserved',()=>{const a=Object.create(null);for(const k of ['__proto__','constructor','prototype','😀','\ud800'])Object.defineProperty(a,k,{value:k,enumerable:true,writable:true,configurable:true});return a}],['binary-8m',()=>binary(8388608)]];
