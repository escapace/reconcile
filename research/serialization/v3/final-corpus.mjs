import {cases,workloads as previous} from './corpus.mjs';
export {cases,equivalent} from './corpus.mjs';
export const workloads={...previous,'mixed-small-buffers':()=>Array.from({length:1000},(_,i)=>{const bytes=new Uint8Array(64);for(let j=0;j<64;j++)bytes[j]=(i*23+j*17)&255;return {id:i,label:'record-'+i,buffer:bytes.buffer,view:bytes}})};
