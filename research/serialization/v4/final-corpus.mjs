export {equivalent,cases} from '../v3/final-corpus.mjs';
import {workloads as old} from '../v3/final-corpus.mjs';
// Supplemental, labelled diagnostic: no changes to existing workloads.
// 512 records, each with 16 references drawn from the same 64-object pool.
export const workloads={...old,'dense-dag':()=>{const pool=Array.from({length:64},(_,i)=>({id:i,label:'pool-'+i}));return Array.from({length:512},(_,i)=>({id:i,refs:Array.from({length:16},(_,j)=>pool[(i*7+j*11)%pool.length])}));}};
