import { ordinaryRecord, nullRecord } from './record'
import { denseArray, sparseArray } from './array'
import { map, set } from './collection'
import { date, buffer, view, url, parameters, temporal } from './native'
export const decoders = [
  ordinaryRecord,
  nullRecord,
  denseArray,
  sparseArray,
  map,
  set,
  date,
  buffer,
  view,
  url,
  parameters,
  temporal,
]
