import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Match View v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqPsxequitiesMatchviewAsciiitchV11

/-- Best Bid And Offer Message: 28 bytes -/
structure BestBidAndOfferMessage where
  symbol : Alpha 8
  bidPrice : Alpha 10
  askPrice : Alpha 10
  deriving DecidableEq, Repr

namespace BestBidAndOfferMessage

def encode (message : BestBidAndOfferMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.bidPrice
    ++ (Alpha.encode message.askPrice))

def decode (bytes : List UInt8) : Option (BestBidAndOfferMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (bidPrice, bytes) ← Alpha.decode 10 bytes
  let (askPrice, bytes) ← Alpha.decode 10 bytes
  pure ({ symbol, bidPrice, askPrice }, bytes)

@[simp] theorem encode_length (message : BestBidAndOfferMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BestBidAndOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestBidAndOfferMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BestBidAndOfferMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | bestBidAndOfferMessage (message : BestBidAndOfferMessage) -- "U" 0x55
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .bestBidAndOfferMessage _ => 85

def encode : Payload → List UInt8
  | .bestBidAndOfferMessage message => BestBidAndOfferMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 28 := by
  cases message with
  | bestBidAndOfferMessage inner =>
    simp only [encode, BestBidAndOfferMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 85 then (BestBidAndOfferMessage.decode bytes).map fun (message, rest) => (.bestBidAndOfferMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  timestamp : Alpha 8
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  Alpha.encode message.timestamp
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (timestamp, bytes) ← Alpha.decode 8 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ timestamp, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | bestBidAndOfferMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, BestBidAndOfferMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequenceNumber : BitVec 32
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 4 message.sequenceNumber
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUInt 4 bytes
  let (messageCount, bytes) ← decodeUIntLE 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NasdaqPsxequitiesMatchviewAsciiitchV11
