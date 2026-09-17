import Omi.Wire

/-!
# Investors Exchange Top Of Book v1.56

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: Quote Update Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Sale Condition Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.IexIexequitiesTopsIextpV156

/-- Quote Update Message: 41 bytes -/
structure QuoteUpdateMessage where
  quoteUpdateFlags : BitVec 8
  timestamp : BitVec 64
  symbol : Alpha 8
  bidSize : BitVec 32
  bidPrice : BitVec 64
  askPrice : BitVec 64
  askSize : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteUpdateMessage

def encode (message : QuoteUpdateMessage) : List UInt8 :=
  encodeUIntLE 1 message.quoteUpdateFlags
    ++ (encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.bidSize
    ++ (encodeUIntLE 8 message.bidPrice
    ++ (encodeUIntLE 8 message.askPrice
    ++ (encodeUIntLE 4 message.askSize))))))

def decode (bytes : List UInt8) : Option (QuoteUpdateMessage × List UInt8) := do
  let (quoteUpdateFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 8 bytes
  let (askPrice, bytes) ← decodeUIntLE 8 bytes
  let (askSize, bytes) ← decodeUIntLE 4 bytes
  pure ({ quoteUpdateFlags, timestamp, symbol, bidSize, bidPrice, askPrice, askSize }, bytes)

@[simp] theorem encode_length (message : QuoteUpdateMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteUpdateMessage

/-- Trade Report Message: 41 bytes -/
structure TradeReportMessage where
  saleConditionFlags : BitVec 8
  timestamp : BitVec 64
  symbol : Alpha 8
  size : BitVec 32
  price : BitVec 64
  tradeId : BitVec 64
  reserved4 : BitVec 32
  deriving DecidableEq, Repr

namespace TradeReportMessage

def encode (message : TradeReportMessage) : List UInt8 :=
  encodeUIntLE 1 message.saleConditionFlags
    ++ (encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 4 message.reserved4))))))

def decode (bytes : List UInt8) : Option (TradeReportMessage × List UInt8) := do
  let (saleConditionFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (reserved4, bytes) ← decodeUIntLE 4 bytes
  pure ({ saleConditionFlags, timestamp, symbol, size, price, tradeId, reserved4 }, bytes)

@[simp] theorem encode_length (message : TradeReportMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeReportMessage

/-- Trade Break Message: 41 bytes -/
structure TradeBreakMessage where
  saleConditionFlags : BitVec 8
  timestamp : BitVec 64
  symbol : Alpha 8
  size : BitVec 32
  price : BitVec 64
  tradeId : BitVec 64
  reserved4 : BitVec 32
  deriving DecidableEq, Repr

namespace TradeBreakMessage

def encode (message : TradeBreakMessage) : List UInt8 :=
  encodeUIntLE 1 message.saleConditionFlags
    ++ (encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 4 message.reserved4))))))

def decode (bytes : List UInt8) : Option (TradeBreakMessage × List UInt8) := do
  let (saleConditionFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (reserved4, bytes) ← decodeUIntLE 4 bytes
  pure ({ saleConditionFlags, timestamp, symbol, size, price, tradeId, reserved4 }, bytes)

@[simp] theorem encode_length (message : TradeBreakMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeBreakMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBreakMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeBreakMessage

/-- Any Message Data, selected by Message Type -/
inductive MessageData where
  | quoteUpdateMessage (message : QuoteUpdateMessage) -- 'Q' 0x51
  | tradeReportMessage (message : TradeReportMessage) -- 'T' 0x54
  | tradeBreakMessage (message : TradeBreakMessage) -- 'B' 0x42
  deriving DecidableEq, Repr

namespace MessageData

/-- The Message Type each message is sent under -/
def tag : MessageData → BitVec 8
  | .quoteUpdateMessage _ => 81
  | .tradeReportMessage _ => 84
  | .tradeBreakMessage _ => 66

def encode : MessageData → List UInt8
  | .quoteUpdateMessage message => QuoteUpdateMessage.encode message
  | .tradeReportMessage message => TradeReportMessage.encode message
  | .tradeBreakMessage message => TradeBreakMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (MessageData × List UInt8) :=
  if tag = 81 then (QuoteUpdateMessage.decode bytes).map fun (message, rest) => (.quoteUpdateMessage message, rest)
  else if tag = 84 then (TradeReportMessage.decode bytes).map fun (message, rest) => (.tradeReportMessage message, rest)
  else if tag = 66 then (TradeBreakMessage.decode bytes).map fun (message, rest) => (.tradeBreakMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageData) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageData

/-- Message -/
structure Message where
  messageData : MessageData
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (MessageData.tag message.messageData)
    ++ (MessageData.encode message.messageData)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (messageData, bytes) ← MessageData.decode messageType bytes
  pure ({ messageData }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MessageData.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.messageData with
  | quoteUpdateMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, QuoteUpdateMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, TradeReportMessage.encode_length]
    omega
  | tradeBreakMessage inner =>
    simp only [MessageData.encode, List.length_append, encodeUInt_length, TradeBreakMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 0 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  version : BitVec 8
  reserved : Alpha 1
  messageProtocolId : BitVec 16
  channelId : BitVec 32
  sessionId : BitVec 32
  payloadLength : BitVec 16
  streamOffset : BitVec 64
  firstMessageSequenceNumber : BitVec 64
  sendTime : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 1 message.version
    ++ (Alpha.encode message.reserved
    ++ (encodeUIntLE 2 message.messageProtocolId
    ++ (encodeUIntLE 4 message.channelId
    ++ (encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 2 message.payloadLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeUIntLE 8 message.streamOffset
    ++ (encodeUIntLE 8 message.firstMessageSequenceNumber
    ++ (encodeUIntLE 8 message.sendTime
    ++ (encodeMany Message.encode message.message.val))))))))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (version, bytes) ← decodeUIntLE 1 bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (messageProtocolId, bytes) ← decodeUIntLE 2 bytes
  let (channelId, bytes) ← decodeUIntLE 4 bytes
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (payloadLength, bytes) ← decodeUIntLE 2 bytes
  let (messageCount, bytes) ← decodeUIntLE 2 bytes
  let (streamOffset, bytes) ← decodeUIntLE 8 bytes
  let (firstMessageSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (sendTime, bytes) ← decodeUIntLE 8 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ version, reserved, messageProtocolId, channelId, sessionId, payloadLength, streamOffset, firstMessageSequenceNumber, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.IexIexequitiesTopsIextpV156
