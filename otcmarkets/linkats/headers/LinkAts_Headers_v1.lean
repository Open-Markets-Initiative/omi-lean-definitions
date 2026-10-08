import Wire

/-!
# OTC Markets Group  v1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.OtcmarketsLinkatsHeadersLinkV1

/-- Message -/
structure Message where
  messageType : BitVec 8
  payload : Capped 65532
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 message.messageType
    ++ (message.payload.val)

def decodeBody (bytes : List UInt8) : Option Message := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let payload_ := bytes
  if fits_payload : payload_.length ≤ 65532 then
    pure { messageType, payload := ⟨payload_, fits_payload⟩ }
  else none

theorem decodeBody_encodeBody (message : Message) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.payload.length_le]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  have bound_payload := message.payload.length_le
  unfold encodeBody
  simp only [List.length_append, encodeUInt_length]
  omega

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedAll 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAll_encodeFramed 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  packetSize : BitVec 16
  seqNum : BitVec 32
  packetFlag : BitVec 8
  packetMilli : BitVec 32
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 message.packetSize
    ++ (encodeUInt 4 message.seqNum
    ++ (encodeUIntLE 1 message.packetFlag
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUInt 4 message.packetMilli
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (packetSize, bytes) ← decodeUInt 2 bytes
  let (seqNum, bytes) ← decodeUInt 4 bytes
  let (packetFlag, bytes) ← decodeUIntLE 1 bytes
  let (messages, bytes) ← decodeUInt 1 bytes
  let (packetMilli, bytes) ← decodeUInt 4 bytes
  let (message_, bytes) ← decodeMany Message.decode messages.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ packetSize, seqNum, packetFlag, packetMilli, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.OtcmarketsLinkatsHeadersLinkV1
