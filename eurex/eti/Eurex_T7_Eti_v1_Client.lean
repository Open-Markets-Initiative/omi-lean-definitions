import Omi.Wire

/-!
# Eurex Exchange Enhanced Trading Interface v1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EurexT7EtiFbeV1Client

/-- Client Message -/
structure ClientMessage where
  templateId : BitVec 16
  deriving DecidableEq, Repr

namespace ClientMessage

def encodeBody (message : ClientMessage) : List UInt8 :=
  encodeUIntLE 2 message.templateId

def decodeBody (bytes : List UInt8) : Option (ClientMessage × List UInt8) := do
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  pure ({ templateId }, bytes)

theorem decodeBody_encodeBody (message : ClientMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientMessage) : (encodeBody message).length + 4 < 256 ^ 4 := by
  unfold encodeBody
  simp only [encodeUIntLE_length]
  omega

/-- Size rule: Body Len counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : ClientMessage → List UInt8 :=
  encodeFramedLE 4 4 encodeBody

def decode : List UInt8 → Option (ClientMessage × List UInt8) :=
  decodeFramedLE 4 4 decodeBody

@[simp] theorem decode_encode (message : ClientMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 4 4 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : ClientMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end ClientMessage

/-- Client Packet -/
structure ClientPacket where
  clientMessage : List ClientMessage
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientMessage.encode message.clientMessage

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientMessage ← decodeAll ClientMessage.decode bytes.length bytes
  pure { clientMessage }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeAll_encodeMany ClientMessage.encode ClientMessage.decode ClientMessage.decode_encode ClientMessage.encode_length_pos message.clientMessage _ (encodeMany_length_ge ClientMessage.encode ClientMessage.encode_length_pos message.clientMessage), Option.bind_some]
  rfl

end ClientPacket

end Omi.EurexT7EtiFbeV1Client
