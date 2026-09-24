import Omi.Wire

/-!
# Texas Stock Exchange  v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TxseTxseequitiesFramingUdpV10

/-- Udp Sequenced Message -/
structure UdpSequencedMessage where
  streamId : BitVec 8
  messageType : BitVec 8
  payload : Capped 65533
  deriving DecidableEq, Repr

namespace UdpSequencedMessage

def encodeBody (message : UdpSequencedMessage) : List UInt8 :=
  encodeUInt 1 message.streamId
    ++ (encodeUInt 1 message.messageType
    ++ (message.payload.val))

def decodeBody (bytes : List UInt8) : Option UdpSequencedMessage := do
  let (streamId, bytes) ← decodeUInt 1 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let payload_ := bytes
  if fits_payload : payload_.length ≤ 65533 then
    pure { streamId, messageType, payload := ⟨payload_, fits_payload⟩ }
  else none

theorem decodeBody_encodeBody (message : UdpSequencedMessage) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.payload.length_le]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : UdpSequencedMessage) : (encodeBody message).length + 0 < 256 ^ 2 := by
  have bound_payload := message.payload.length_le
  unfold encodeBody
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length]
  omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : UdpSequencedMessage → List UInt8 :=
  encodeFramedLE 2 0 encodeBody

def decode : List UInt8 → Option (UdpSequencedMessage × List UInt8) :=
  decodeFramedAllLE 2 0 decodeBody

@[simp] theorem decode_encode (message : UdpSequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : UdpSequencedMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end UdpSequencedMessage

/-- Packet -/
structure Packet where
  session : BitVec 64
  sequence : BitVec 64
  packetType : BitVec 8
  udpSequencedMessage : Bounded 2 UdpSequencedMessage
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 8 message.session
    ++ (encodeUIntLE 8 message.sequence
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.udpSequencedMessage.val.length)
    ++ (encodeUInt 1 message.packetType
    ++ (encodeMany UdpSequencedMessage.encode message.udpSequencedMessage.val))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← decodeUIntLE 8 bytes
  let (sequence, bytes) ← decodeUIntLE 8 bytes
  let (messageCount, bytes) ← decodeUIntLE 2 bytes
  let (packetType, bytes) ← decodeUInt 1 bytes
  let (udpSequencedMessage_, bytes) ← decodeMany UdpSequencedMessage.decode messageCount.toNat bytes
  if fits_udpSequencedMessage : udpSequencedMessage_.length < 256 ^ 2 then
    pure ({ session, sequence, packetType, udpSequencedMessage := ⟨udpSequencedMessage_, fits_udpSequencedMessage⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 UdpSequencedMessage.encode UdpSequencedMessage.decode UdpSequencedMessage.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.udpSequencedMessage.length_lt]
  rfl

end Packet

end Omi.TxseTxseequitiesFramingUdpV10
