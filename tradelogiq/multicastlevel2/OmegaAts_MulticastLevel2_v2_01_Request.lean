import Wire

/-!
# Tradelogiq Markets Inc. Omega Multicast Level 2 v2.01

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TradelogiqOmegaatsMulticastlevel2ItchV201Request

/-- Request Packet: 20 bytes -/
structure RequestPacket where
  requestSession : Alpha 10
  requestSequenceNumber : BitVec 64
  requestedMessageCount : BitVec 16
  deriving DecidableEq, Repr

namespace RequestPacket

def encode (message : RequestPacket) : List UInt8 :=
  Alpha.encode message.requestSession
    ++ (encodeUInt 8 message.requestSequenceNumber
    ++ (encodeUInt 2 message.requestedMessageCount))

def decode (bytes : List UInt8) : Option (RequestPacket × List UInt8) := do
  let (requestSession, bytes) ← Alpha.decode 10 bytes
  let (requestSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (requestedMessageCount, bytes) ← decodeUInt 2 bytes
  pure ({ requestSession, requestSequenceNumber, requestedMessageCount }, bytes)

@[simp] theorem encode_length (message : RequestPacket) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RequestPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RequestPacket

end Omi.TradelogiqOmegaatsMulticastlevel2ItchV201Request
