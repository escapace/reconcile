import{workloads as old,equivalent}from'../corpus.mjs';import{temporalValues}from'../../v2/corpus.mjs';export{equivalent};
export const workloads={...old,'Temporal-exact-200':()=>Array.from({length:25},()=>temporalValues()).flat()};
export const common=['json-small','json-1000','json-10000','numeric-array','negative-array','mixed-signs','string-array','prefix-strings','dag-2000','dense-dag','cycle-300','deep-200','binary-64k','binary-64k-entropy','binary-1m-entropy','mixed-small-buffers','rich','collections'];
export const native=['URL-linked-100','Temporal-exact-200'];export const scenarios=[...common,...native];
