import { deserialize, serialize } from '../../index'

/** Encodes a value as JSON text, as an application sends it. */
export const encodeText = (value: unknown): string => JSON.stringify(serialize(value))

/** Decodes JSON text with no size limit, as for trusted input. */
export const decodeText = (text: string): unknown =>
  deserialize(JSON.parse(text), { maxBytes: Infinity })
