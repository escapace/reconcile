import { isArrayBuffer, isDate, isMap, isSet, isTypedArray } from 'es-toolkit'

const isDataView = (value: unknown): value is DataView => value instanceof DataView

export const OBJECT_KIND_PLAIN = 0
export const OBJECT_KIND_ARRAY = 1
export const OBJECT_KIND_DATE = 2
export const OBJECT_KIND_MAP = 3
export const OBJECT_KIND_SET = 4
export const OBJECT_KIND_ARRAY_BUFFER = 5
export const OBJECT_KIND_DATA_VIEW = 6
export const OBJECT_KIND_TYPED_ARRAY = 7

export type ObjectKind =
  | typeof OBJECT_KIND_ARRAY
  | typeof OBJECT_KIND_ARRAY_BUFFER
  | typeof OBJECT_KIND_DATA_VIEW
  | typeof OBJECT_KIND_DATE
  | typeof OBJECT_KIND_MAP
  | typeof OBJECT_KIND_PLAIN
  | typeof OBJECT_KIND_SET
  | typeof OBJECT_KIND_TYPED_ARRAY

export const objectKindOf = (value: object): ObjectKind => {
  if (Array.isArray(value)) {
    return OBJECT_KIND_ARRAY
  }

  if (isDate(value)) {
    return OBJECT_KIND_DATE
  }

  if (isMap(value)) {
    return OBJECT_KIND_MAP
  }

  if (isSet(value)) {
    return OBJECT_KIND_SET
  }

  if (isArrayBuffer(value)) {
    return OBJECT_KIND_ARRAY_BUFFER
  }

  if (isDataView(value)) {
    return OBJECT_KIND_DATA_VIEW
  }

  if (isTypedArray(value)) {
    return OBJECT_KIND_TYPED_ARRAY
  }

  return OBJECT_KIND_PLAIN
}
