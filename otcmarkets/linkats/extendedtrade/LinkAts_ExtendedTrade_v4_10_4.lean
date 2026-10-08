import Wire

/-!
# OTC Markets Group  v4.10.4

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.OtcmarketsLinkatsExtendedtradeLinkV4104

/-- Start Of Spin Message: 17 bytes -/
structure StartOfSpinMessage where
  channelSeqNum : BitVec 32
  spinType : BitVec 8
  spinStartTimeMilli : BitVec 64
  spinLastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace StartOfSpinMessage

def encode (message : StartOfSpinMessage) : List UInt8 :=
  encodeUInt 4 message.channelSeqNum
    ++ (encodeUInt 1 message.spinType
    ++ (encodeUInt 8 message.spinStartTimeMilli
    ++ (encodeUInt 4 message.spinLastSeqNum)))

def decode (bytes : List UInt8) : Option (StartOfSpinMessage × List UInt8) := do
  let (channelSeqNum, bytes) ← decodeUInt 4 bytes
  let (spinType, bytes) ← decodeUInt 1 bytes
  let (spinStartTimeMilli, bytes) ← decodeUInt 8 bytes
  let (spinLastSeqNum, bytes) ← decodeUInt 4 bytes
  pure ({ channelSeqNum, spinType, spinStartTimeMilli, spinLastSeqNum }, bytes)

@[simp] theorem encode_length (message : StartOfSpinMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StartOfSpinMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfSpinMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfSpinMessage

/-- End Of Spin Message: 21 bytes -/
structure EndOfSpinMessage where
  channelSeqNum : BitVec 32
  spinType : BitVec 8
  spinMsgCt : BitVec 32
  spinEndTimeMilli : BitVec 64
  spinLastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace EndOfSpinMessage

def encode (message : EndOfSpinMessage) : List UInt8 :=
  encodeUInt 4 message.channelSeqNum
    ++ (encodeUInt 1 message.spinType
    ++ (encodeUInt 4 message.spinMsgCt
    ++ (encodeUInt 8 message.spinEndTimeMilli
    ++ (encodeUInt 4 message.spinLastSeqNum))))

def decode (bytes : List UInt8) : Option (EndOfSpinMessage × List UInt8) := do
  let (channelSeqNum, bytes) ← decodeUInt 4 bytes
  let (spinType, bytes) ← decodeUInt 1 bytes
  let (spinMsgCt, bytes) ← decodeUInt 4 bytes
  let (spinEndTimeMilli, bytes) ← decodeUInt 8 bytes
  let (spinLastSeqNum, bytes) ← decodeUInt 4 bytes
  pure ({ channelSeqNum, spinType, spinMsgCt, spinEndTimeMilli, spinLastSeqNum }, bytes)

@[simp] theorem encode_length (message : EndOfSpinMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : EndOfSpinMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfSpinMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndOfSpinMessage

/-- Market Open Message: 20 bytes -/
structure MarketOpenMessage where
  channelSeqNum : BitVec 32
  marketOpen : BitVec 64
  marketClose : BitVec 64
  deriving DecidableEq, Repr

namespace MarketOpenMessage

def encode (message : MarketOpenMessage) : List UInt8 :=
  encodeUInt 4 message.channelSeqNum
    ++ (encodeUInt 8 message.marketOpen
    ++ (encodeUInt 8 message.marketClose))

def decode (bytes : List UInt8) : Option (MarketOpenMessage × List UInt8) := do
  let (channelSeqNum, bytes) ← decodeUInt 4 bytes
  let (marketOpen, bytes) ← decodeUInt 8 bytes
  let (marketClose, bytes) ← decodeUInt 8 bytes
  pure ({ channelSeqNum, marketOpen, marketClose }, bytes)

@[simp] theorem encode_length (message : MarketOpenMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : MarketOpenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketOpenMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketOpenMessage

/-- Market Close Message: 16 bytes -/
structure MarketCloseMessage where
  channelSeqNum : BitVec 32
  marketCloseTimeMilli : BitVec 64
  marketMsgCt : BitVec 32
  deriving DecidableEq, Repr

namespace MarketCloseMessage

def encode (message : MarketCloseMessage) : List UInt8 :=
  encodeUInt 4 message.channelSeqNum
    ++ (encodeUInt 8 message.marketCloseTimeMilli
    ++ (encodeUInt 4 message.marketMsgCt))

def decode (bytes : List UInt8) : Option (MarketCloseMessage × List UInt8) := do
  let (channelSeqNum, bytes) ← decodeUInt 4 bytes
  let (marketCloseTimeMilli, bytes) ← decodeUInt 8 bytes
  let (marketMsgCt, bytes) ← decodeUInt 4 bytes
  pure ({ channelSeqNum, marketCloseTimeMilli, marketMsgCt }, bytes)

@[simp] theorem encode_length (message : MarketCloseMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : MarketCloseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketCloseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketCloseMessage

/-- Extended Trade Message: 51 bytes -/
structure ExtendedTradeMessage where
  channelSeqNum : BitVec 32
  tradeId : BitVec 64
  tradeAction : BitVec 8
  tradeFlags : BitVec 8
  securityId : BitVec 32
  tradeStatus : BitVec 8
  venue : Alpha 3
  deprecatedUtf85 : Alpha 5
  tradePrice : BitVec 64
  tradeSize : BitVec 64
  tradeTimeMilli : BitVec 64
  deriving DecidableEq, Repr

namespace ExtendedTradeMessage

def encode (message : ExtendedTradeMessage) : List UInt8 :=
  encodeUInt 4 message.channelSeqNum
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 1 message.tradeAction
    ++ (encodeUInt 1 message.tradeFlags
    ++ (encodeUInt 4 message.securityId
    ++ (encodeUIntLE 1 message.tradeStatus
    ++ (Alpha.encode message.venue
    ++ (Alpha.encode message.deprecatedUtf85
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 8 message.tradeSize
    ++ (encodeUInt 8 message.tradeTimeMilli))))))))))

def decode (bytes : List UInt8) : Option (ExtendedTradeMessage × List UInt8) := do
  let (channelSeqNum, bytes) ← decodeUInt 4 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (tradeAction, bytes) ← decodeUInt 1 bytes
  let (tradeFlags, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← decodeUInt 4 bytes
  let (tradeStatus, bytes) ← decodeUIntLE 1 bytes
  let (venue, bytes) ← Alpha.decode 3 bytes
  let (deprecatedUtf85, bytes) ← Alpha.decode 5 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeSize, bytes) ← decodeUInt 8 bytes
  let (tradeTimeMilli, bytes) ← decodeUInt 8 bytes
  pure ({ channelSeqNum, tradeId, tradeAction, tradeFlags, securityId, tradeStatus, venue, deprecatedUtf85, tradePrice, tradeSize, tradeTimeMilli }, bytes)

@[simp] theorem encode_length (message : ExtendedTradeMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ExtendedTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExtendedTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExtendedTradeMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | startOfSpinMessage (message : StartOfSpinMessage) -- 11
  | endOfSpinMessage (message : EndOfSpinMessage) -- 12
  | marketOpenMessage (message : MarketOpenMessage) -- 13
  | marketCloseMessage (message : MarketCloseMessage) -- 14
  | extendedTradeMessage (message : ExtendedTradeMessage) -- 18
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .startOfSpinMessage _ => 11
  | .endOfSpinMessage _ => 12
  | .marketOpenMessage _ => 13
  | .marketCloseMessage _ => 14
  | .extendedTradeMessage _ => 18

def encode : Payload → List UInt8
  | .startOfSpinMessage message => StartOfSpinMessage.encode message
  | .endOfSpinMessage message => EndOfSpinMessage.encode message
  | .marketOpenMessage message => MarketOpenMessage.encode message
  | .marketCloseMessage message => MarketCloseMessage.encode message
  | .extendedTradeMessage message => ExtendedTradeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 51 := by
  cases message with
  | startOfSpinMessage inner =>
    simp only [encode, StartOfSpinMessage.encode_length]
    omega
  | endOfSpinMessage inner =>
    simp only [encode, EndOfSpinMessage.encode_length]
    omega
  | marketOpenMessage inner =>
    simp only [encode, MarketOpenMessage.encode_length]
    omega
  | marketCloseMessage inner =>
    simp only [encode, MarketCloseMessage.encode_length]
    omega
  | extendedTradeMessage inner =>
    simp only [encode, ExtendedTradeMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 11 then (StartOfSpinMessage.decode bytes).map fun (message, rest) => (.startOfSpinMessage message, rest)
  else if tag = 12 then (EndOfSpinMessage.decode bytes).map fun (message, rest) => (.endOfSpinMessage message, rest)
  else if tag = 13 then (MarketOpenMessage.decode bytes).map fun (message, rest) => (.marketOpenMessage message, rest)
  else if tag = 14 then (MarketCloseMessage.decode bytes).map fun (message, rest) => (.marketCloseMessage message, rest)
  else if tag = 18 then (ExtendedTradeMessage.decode bytes).map fun (message, rest) => (.extendedTradeMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | startOfSpinMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StartOfSpinMessage.encode_length]
    omega
  | endOfSpinMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EndOfSpinMessage.encode_length]
    omega
  | marketOpenMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOpenMessage.encode_length]
    omega
  | marketCloseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketCloseMessage.encode_length]
    omega
  | extendedTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExtendedTradeMessage.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

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

end Omi.OtcmarketsLinkatsExtendedtradeLinkV4104
