import Omi.Wire

/-!
# Aquis Exchange Tcp Headers v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.AquisAquisequitiesTcpheaderAtpV10

/-- Message -/
structure Message where
  msgType : BitVec 8
  msgSeqNo : BitVec 32
  payload : Capped 65528
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 message.msgType
    ++ (encodeUIntLE 4 message.msgSeqNo
    ++ (message.payload.val))

def decodeBody (bytes : List UInt8) : Option Message := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  let (msgSeqNo, bytes) ← decodeUIntLE 4 bytes
  let payload_ := bytes
  if fits_payload : payload_.length ≤ 65528 then
    pure { msgType, msgSeqNo, payload := ⟨payload_, fits_payload⟩ }
  else none

theorem decodeBody_encodeBody (message : Message) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [dite_eq_left message.payload.length_le]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  have bound_payload := message.payload.length_le
  unfold encodeBody
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedAllLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option Packet := do
  let message ← decodeAll Message.decode bytes.length bytes
  pure { message }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end Packet

end Omi.AquisAquisequitiesTcpheaderAtpV10
