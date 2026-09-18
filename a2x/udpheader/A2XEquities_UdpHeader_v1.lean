import Omi.Wire

/-!
# A2X Markets Udp Headers v1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.A2xA2xequitiesUdpheaderAmdV1

/-- Message -/
structure Message where
  msgType : BitVec 8
  seqNo : BitVec 32
  payload : Capped 249
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 4 message.seqNo
    ++ (message.payload.val)

def decodeBody (msgType : BitVec 8) (bytes : List UInt8) : Option Message := do
  let (seqNo, bytes) ← decodeUInt 4 bytes
  let payload_ := bytes
  if fits_payload : payload_.length ≤ 249 then
    pure { msgType, seqNo, payload := ⟨payload_, fits_payload⟩ }
  else none

theorem decodeBody_encodeBody (message : Message) : decodeBody message.msgType (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.payload.length_le]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 1 := by
  have bound_payload := message.payload.length_le
  unfold encodeBody
  simp only [List.length_append, encodeUInt_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body and checked on decode; Msg Type is read ahead of it -/
def encode (message : Message) : List UInt8 :=
  encodeUInt 1 message.msgType
    ++ (encodeFramed 1 2 encodeBody message)

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  decodeFramedAll 1 2 (decodeBody msgType) bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  exact decodeFramedAll_encodeFramed 1 2 encodeBody (decodeBody message.msgType) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (messageCount, bytes) ← decodeUInt 1 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.A2xA2xequitiesUdpheaderAmdV1
