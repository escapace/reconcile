import { ordinaryRecord, nullRecord } from './record'
import { denseArray, sparseArray } from './array'
import { map, set } from './collection'
import {
  date,
  buffer,
  view,
  url,
  parameters,
  ownedParameters,
  temporal,
  scalar,
  bigint,
} from './native'
// Indexed by node tag (layout.ts).
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
  ownedParameters,
  temporal,
  scalar,
  scalar,
  scalar,
  scalar,
  scalar,
  bigint,
]
