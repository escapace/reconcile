import{workloads as common,native}from'../v5/confirm/corpus.mjs';export{native};
export const workloads={...common,'dates-2000':()=>Array.from({length:2000},(_,i)=>new Date(i))};
export const ablations=['json-1000','dag-2000','collections','numeric-array','string-array','dates-2000','mixed-small-buffers','Temporal-exact-200'];
export const confirmation=['json-small','json-1000','json-10000','dag-2000','dense-dag','cycle-300','deep-200','collections','numeric-array','string-array','dates-2000','rich','mixed-small-buffers','binary-1m-entropy','URL-linked-100','Temporal-exact-200'];
