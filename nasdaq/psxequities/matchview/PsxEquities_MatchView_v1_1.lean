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

/-- End Of Session: 0 bytes -/
structure EndOfSession where
  deriving DecidableEq, Repr

namespace EndOfSession

def encode (_ : EndOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end EndOfSession

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

/-- Message Data -/
structure MessageData where
  timestamp : Alpha 8
  payload : Payload
  deriving DecidableEq, Repr

namespace MessageData

def encode (message : MessageData) : List UInt8 :=
  Alpha.encode message.timestamp
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decode (bytes : List UInt8) : Option (MessageData × List UInt8) := do
  let (timestamp, bytes) ← Alpha.decode 8 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ timestamp, payload }, bytes)

theorem encode_length_pos (message : MessageData) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MessageData) : (encode message).length ≤ 37 := by
  unfold encode
  cases message.payload with
  | bestBidAndOfferMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, BestBidAndOfferMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : MessageData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end MessageData

/-- Any Message Body, selected by Message Length -/
inductive MessageBody where
  | endOfSession (message : EndOfSession) -- 0
  | messageData (message : Fallback MessageData.encode 16 [0]) -- any other value: the bytes it counts
  deriving DecidableEq, Repr

namespace MessageBody

/-- The Message Length each message is sent under -/
def tag : MessageBody → BitVec 16
  | .endOfSession _ => 0
  | .messageData message => message.key

def encode : MessageBody → List UInt8
  | .endOfSession message => EndOfSession.encode message
  | .messageData message => MessageData.encode message.val

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession : MessageBody → Bool
  | .endOfSession _ => true
  | _ => false

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 37 := by
  cases message with
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega
  | messageData inner =>
    have bound_inner := MessageData.encode_length_le inner.val
    simp only [encode]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessageBody × List UInt8) :=
  if tag = 0 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
  else (decodeFallback 16 [0] MessageData.encode MessageData.decode tag.toNat bytes).map fun (message, rest) => (.messageData message, rest)

@[simp] theorem decode_encode (message : MessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message with
  | endOfSession m => simp [decode, encode, tag]
  | messageData m =>
    have unlisted_0 : m.key ≠ 0 := m.key_ne 0 (by decide) (by decide)
    dsimp only [decode, encode, tag]
    rw [ite_eq_right unlisted_0, decodeFallback_encode 16 [0] MessageData.encode MessageData.decode m (MessageData.decode_encode m.val)]
    rfl

end MessageBody

/-- Message -/
structure Message where
  messageBody : MessageBody
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 (MessageBody.tag message.messageBody)
    ++ (MessageBody.encode message.messageBody)

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageLength, bytes) ← decodeUIntLE 2 bytes
  let (messageBody, bytes) ← MessageBody.decode messageLength bytes
  pure ({ messageBody }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 39 := by
  unfold encode
  cases message.messageBody with
  | endOfSession inner =>
    simp only [MessageBody.encode, List.length_append, encodeUIntLE_length, EndOfSession.encode_length]
    omega
  | messageData inner =>
    have bound_inner := MessageData.encode_length_le inner.val
    simp only [MessageBody.encode, List.length_append, encodeUIntLE_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [MessageBody.decode_encode, some_bind]
  rfl

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession (message : Message) : Bool :=
  MessageBody.endsSession message.messageBody

end Message

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequenceNumber : BitVec 32
  message : Bounded 2 Message
  message_last : endsLast Message.endsSession message.val = true
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (messageCount, bytes) ← decodeUIntLE 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    if last_message : endsLast Message.endsSession message_ = true then
      pure ({ session, sequenceNumber, message := ⟨message_, fits_message⟩, message_last := last_message }, bytes)
    else none
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 2555881 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 39 Message.encode_length_le message.message.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt, dite_eq_left message.message_last]
  rfl

end Packet

end Omi.NasdaqPsxequitiesMatchviewAsciiitchV11
