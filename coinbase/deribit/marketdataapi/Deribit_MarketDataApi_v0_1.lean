import Omi.Wire

/-!
# Coinbase Market Data Api v0.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Packet Type is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: a Message Count of 0 marks Empty Packet and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: Message Flags is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Flags is a bit field set, proven as its 4 byte integer rather than bit by bit.

Note: Taker Flags is a bit field set, proven as its 4 byte integer rather than bit by bit.

Note: Maker Flags is a bit field set, proven as its 4 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CoinbaseDeribitMarketdataapiSbeV01

/-- Logical Expiry: 8 bytes -/
structure LogicalExpiry where
  year : BitVec 16
  month : BitVec 16
  weekOfMonth : BitVec 16
  dayOfMonth : BitVec 16
  deriving DecidableEq, Repr

namespace LogicalExpiry

def encode (message : LogicalExpiry) : List UInt8 :=
  encodeUIntLE 2 message.year
    ++ (encodeUIntLE 2 message.month
    ++ (encodeUIntLE 2 message.weekOfMonth
    ++ (encodeUIntLE 2 message.dayOfMonth)))

def decode (bytes : List UInt8) : Option (LogicalExpiry × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 2 bytes
  let (month, bytes) ← decodeUIntLE 2 bytes
  let (weekOfMonth, bytes) ← decodeUIntLE 2 bytes
  let (dayOfMonth, bytes) ← decodeUIntLE 2 bytes
  pure ({ year, month, weekOfMonth, dayOfMonth }, bytes)

@[simp] theorem encode_length (message : LogicalExpiry) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LogicalExpiry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogicalExpiry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogicalExpiry

/-- Instrument Message: 303 bytes -/
structure InstrumentMessage where
  instrumentId : BitVec 64
  symbol : Alpha 64
  name : Alpha 128
  baseCurrency : Alpha 8
  quoteCurrency : Alpha 8
  baseIncrement : BitVec 64
  tickSize : BitVec 64
  strikePrice : BitVec 64
  largeTickSize0 : BitVec 64
  largeTickThreshold0 : BitVec 64
  largeTickSize1 : BitVec 64
  largeTickThreshold1 : BitVec 64
  creationTime : BitVec 64
  expiryTime : BitVec 64
  logicalExpiry : LogicalExpiry
  flags : BitVec 32
  type : BitVec 8
  status : BitVec 8
  quantityExponent : BitVec 8
  deriving DecidableEq, Repr

namespace InstrumentMessage

def encode (message : InstrumentMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.name
    ++ (Alpha.encode message.baseCurrency
    ++ (Alpha.encode message.quoteCurrency
    ++ (encodeUIntLE 8 message.baseIncrement
    ++ (encodeUIntLE 8 message.tickSize
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 8 message.largeTickSize0
    ++ (encodeUIntLE 8 message.largeTickThreshold0
    ++ (encodeUIntLE 8 message.largeTickSize1
    ++ (encodeUIntLE 8 message.largeTickThreshold1
    ++ (encodeUIntLE 8 message.creationTime
    ++ (encodeUIntLE 8 message.expiryTime
    ++ (LogicalExpiry.encode message.logicalExpiry
    ++ (encodeUIntLE 4 message.flags
    ++ (encodeUInt 1 message.type
    ++ (encodeUInt 1 message.status
    ++ (encodeUInt 1 message.quantityExponent))))))))))))))))))

def decode (bytes : List UInt8) : Option (InstrumentMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 64 bytes
  let (name, bytes) ← Alpha.decode 128 bytes
  let (baseCurrency, bytes) ← Alpha.decode 8 bytes
  let (quoteCurrency, bytes) ← Alpha.decode 8 bytes
  let (baseIncrement, bytes) ← decodeUIntLE 8 bytes
  let (tickSize, bytes) ← decodeUIntLE 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (largeTickSize0, bytes) ← decodeUIntLE 8 bytes
  let (largeTickThreshold0, bytes) ← decodeUIntLE 8 bytes
  let (largeTickSize1, bytes) ← decodeUIntLE 8 bytes
  let (largeTickThreshold1, bytes) ← decodeUIntLE 8 bytes
  let (creationTime, bytes) ← decodeUIntLE 8 bytes
  let (expiryTime, bytes) ← decodeUIntLE 8 bytes
  let (logicalExpiry, bytes) ← LogicalExpiry.decode bytes
  let (flags, bytes) ← decodeUIntLE 4 bytes
  let (type, bytes) ← decodeUInt 1 bytes
  let (status, bytes) ← decodeUInt 1 bytes
  let (quantityExponent, bytes) ← decodeUInt 1 bytes
  pure ({ instrumentId, symbol, name, baseCurrency, quoteCurrency, baseIncrement, tickSize, strikePrice, largeTickSize0, largeTickThreshold0, largeTickSize1, largeTickThreshold1, creationTime, expiryTime, logicalExpiry, flags, type, status, quantityExponent }, bytes)

@[simp] theorem encode_length (message : InstrumentMessage) : (encode message).length = 303 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LogicalExpiry.encode_length, encodeUInt_length]

theorem encode_length_pos (message : InstrumentMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LogicalExpiry.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InstrumentMessage

/-- Trading Status Update Message: 9 bytes -/
structure TradingStatusUpdateMessage where
  instrumentId : BitVec 64
  tradingStatus : BitVec 8
  deriving DecidableEq, Repr

namespace TradingStatusUpdateMessage

def encode (message : TradingStatusUpdateMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (encodeUInt 1 message.tradingStatus)

def decode (bytes : List UInt8) : Option (TradingStatusUpdateMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (tradingStatus, bytes) ← decodeUInt 1 bytes
  pure ({ instrumentId, tradingStatus }, bytes)

@[simp] theorem encode_length (message : TradingStatusUpdateMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TradingStatusUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingStatusUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradingStatusUpdateMessage

/-- Instrument Info Message: 40 bytes -/
structure InstrumentInfoMessage where
  instrumentId : BitVec 64
  minSellPrice : BitVec 64
  maxBuyPrice : BitVec 64
  indexPrice : BitVec 64
  markPrice : BitVec 64
  deriving DecidableEq, Repr

namespace InstrumentInfoMessage

def encode (message : InstrumentInfoMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.minSellPrice
    ++ (encodeUIntLE 8 message.maxBuyPrice
    ++ (encodeUIntLE 8 message.indexPrice
    ++ (encodeUIntLE 8 message.markPrice))))

def decode (bytes : List UInt8) : Option (InstrumentInfoMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (minSellPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxBuyPrice, bytes) ← decodeUIntLE 8 bytes
  let (indexPrice, bytes) ← decodeUIntLE 8 bytes
  let (markPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, minSellPrice, maxBuyPrice, indexPrice, markPrice }, bytes)

@[simp] theorem encode_length (message : InstrumentInfoMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : InstrumentInfoMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentInfoMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InstrumentInfoMessage

/-- Instrument Ref Message: 48 bytes -/
structure InstrumentRefMessage where
  instrumentId : BitVec 64
  currentFunding : Alpha 8
  funding8h : Alpha 8
  estimatedDeliveryPrice : BitVec 64
  deliveryPrice : BitVec 64
  settlementPrice : BitVec 64
  deriving DecidableEq, Repr

namespace InstrumentRefMessage

def encode (message : InstrumentRefMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (Alpha.encode message.currentFunding
    ++ (Alpha.encode message.funding8h
    ++ (encodeUIntLE 8 message.estimatedDeliveryPrice
    ++ (encodeUIntLE 8 message.deliveryPrice
    ++ (encodeUIntLE 8 message.settlementPrice)))))

def decode (bytes : List UInt8) : Option (InstrumentRefMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (currentFunding, bytes) ← Alpha.decode 8 bytes
  let (funding8h, bytes) ← Alpha.decode 8 bytes
  let (estimatedDeliveryPrice, bytes) ← decodeUIntLE 8 bytes
  let (deliveryPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, currentFunding, funding8h, estimatedDeliveryPrice, deliveryPrice, settlementPrice }, bytes)

@[simp] theorem encode_length (message : InstrumentRefMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentRefMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentRefMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InstrumentRefMessage

/-- Bid Put Message: 32 bytes -/
structure BidPutMessage where
  orderId : BitVec 64
  instrumentId : BitVec 64
  quantityMantissa : BitVec 64
  price : BitVec 64
  deriving DecidableEq, Repr

namespace BidPutMessage

def encode (message : BidPutMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.quantityMantissa
    ++ (encodeUIntLE 8 message.price)))

def decode (bytes : List UInt8) : Option (BidPutMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (quantityMantissa, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderId, instrumentId, quantityMantissa, price }, bytes)

@[simp] theorem encode_length (message : BidPutMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BidPutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BidPutMessage

/-- Ask Put Message: 32 bytes -/
structure AskPutMessage where
  orderId : BitVec 64
  instrumentId : BitVec 64
  quantityMantissa : BitVec 64
  price : BitVec 64
  deriving DecidableEq, Repr

namespace AskPutMessage

def encode (message : AskPutMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.quantityMantissa
    ++ (encodeUIntLE 8 message.price)))

def decode (bytes : List UInt8) : Option (AskPutMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (quantityMantissa, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderId, instrumentId, quantityMantissa, price }, bytes)

@[simp] theorem encode_length (message : AskPutMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AskPutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AskPutMessage

/-- Bid Qty Reduced Message: 24 bytes -/
structure BidQtyReducedMessage where
  orderId : BitVec 64
  instrumentId : BitVec 64
  quantityMantissa : BitVec 64
  deriving DecidableEq, Repr

namespace BidQtyReducedMessage

def encode (message : BidQtyReducedMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.quantityMantissa))

def decode (bytes : List UInt8) : Option (BidQtyReducedMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (quantityMantissa, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderId, instrumentId, quantityMantissa }, bytes)

@[simp] theorem encode_length (message : BidQtyReducedMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BidQtyReducedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidQtyReducedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BidQtyReducedMessage

/-- Ask Qty Reduced Message: 24 bytes -/
structure AskQtyReducedMessage where
  orderId : BitVec 64
  instrumentId : BitVec 64
  quantityMantissa : BitVec 64
  deriving DecidableEq, Repr

namespace AskQtyReducedMessage

def encode (message : AskQtyReducedMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.quantityMantissa))

def decode (bytes : List UInt8) : Option (AskQtyReducedMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (quantityMantissa, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderId, instrumentId, quantityMantissa }, bytes)

@[simp] theorem encode_length (message : AskQtyReducedMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AskQtyReducedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskQtyReducedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AskQtyReducedMessage

/-- Bid Delete Message: 16 bytes -/
structure BidDeleteMessage where
  orderId : BitVec 64
  instrumentId : BitVec 64
  deriving DecidableEq, Repr

namespace BidDeleteMessage

def encode (message : BidDeleteMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId)

def decode (bytes : List UInt8) : Option (BidDeleteMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderId, instrumentId }, bytes)

@[simp] theorem encode_length (message : BidDeleteMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BidDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BidDeleteMessage

/-- Ask Delete Message: 16 bytes -/
structure AskDeleteMessage where
  orderId : BitVec 64
  instrumentId : BitVec 64
  deriving DecidableEq, Repr

namespace AskDeleteMessage

def encode (message : AskDeleteMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId)

def decode (bytes : List UInt8) : Option (AskDeleteMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderId, instrumentId }, bytes)

@[simp] theorem encode_length (message : AskDeleteMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AskDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AskDeleteMessage

/-- Trade Summary Message: 60 bytes -/
structure TradeSummaryMessage where
  instrumentId : BitVec 64
  takerOrderId : BitVec 64
  totalFilledMantissa : BitVec 64
  deepestPrice : BitVec 64
  markPrice : BitVec 64
  indexPrice : BitVec 64
  impliedVolatility : Alpha 8
  takerFlags : BitVec 32
  deriving DecidableEq, Repr

namespace TradeSummaryMessage

def encode (message : TradeSummaryMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.takerOrderId
    ++ (encodeUIntLE 8 message.totalFilledMantissa
    ++ (encodeUIntLE 8 message.deepestPrice
    ++ (encodeUIntLE 8 message.markPrice
    ++ (encodeUIntLE 8 message.indexPrice
    ++ (Alpha.encode message.impliedVolatility
    ++ (encodeUIntLE 4 message.takerFlags)))))))

def decode (bytes : List UInt8) : Option (TradeSummaryMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (takerOrderId, bytes) ← decodeUIntLE 8 bytes
  let (totalFilledMantissa, bytes) ← decodeUIntLE 8 bytes
  let (deepestPrice, bytes) ← decodeUIntLE 8 bytes
  let (markPrice, bytes) ← decodeUIntLE 8 bytes
  let (indexPrice, bytes) ← decodeUIntLE 8 bytes
  let (impliedVolatility, bytes) ← Alpha.decode 8 bytes
  let (takerFlags, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrumentId, takerOrderId, totalFilledMantissa, deepestPrice, markPrice, indexPrice, impliedVolatility, takerFlags }, bytes)

@[simp] theorem encode_length (message : TradeSummaryMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeSummaryMessage

/-- Trade Message: 44 bytes -/
structure TradeMessage where
  matchId : BitVec 64
  instrumentId : BitVec 64
  makerOrderId : BitVec 64
  fillQtyMantissa : BitVec 64
  fillPrice : BitVec 64
  makerFlags : BitVec 32
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.makerOrderId
    ++ (encodeUIntLE 8 message.fillQtyMantissa
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (encodeUIntLE 4 message.makerFlags)))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (makerOrderId, bytes) ← decodeUIntLE 8 bytes
  let (fillQtyMantissa, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (makerFlags, bytes) ← decodeUIntLE 4 bytes
  pure ({ matchId, instrumentId, makerOrderId, fillQtyMantissa, fillPrice, makerFlags }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMessage

/-- Block Trade Message: 78 bytes -/
structure BlockTradeMessage where
  matchId : BitVec 64
  instrumentId : BitVec 64
  blockTradeId : BitVec 64
  blockRfqId : BitVec 64
  fillQtyMantissa : BitVec 64
  fillPrice : BitVec 64
  markPrice : BitVec 64
  indexPrice : BitVec 64
  impliedVolatility : Alpha 8
  takerFlags : BitVec 32
  numberOfLegs : BitVec 16
  deriving DecidableEq, Repr

namespace BlockTradeMessage

def encode (message : BlockTradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.blockTradeId
    ++ (encodeUIntLE 8 message.blockRfqId
    ++ (encodeUIntLE 8 message.fillQtyMantissa
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (encodeUIntLE 8 message.markPrice
    ++ (encodeUIntLE 8 message.indexPrice
    ++ (Alpha.encode message.impliedVolatility
    ++ (encodeUIntLE 4 message.takerFlags
    ++ (encodeUIntLE 2 message.numberOfLegs))))))))))

def decode (bytes : List UInt8) : Option (BlockTradeMessage × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (blockTradeId, bytes) ← decodeUIntLE 8 bytes
  let (blockRfqId, bytes) ← decodeUIntLE 8 bytes
  let (fillQtyMantissa, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (markPrice, bytes) ← decodeUIntLE 8 bytes
  let (indexPrice, bytes) ← decodeUIntLE 8 bytes
  let (impliedVolatility, bytes) ← Alpha.decode 8 bytes
  let (takerFlags, bytes) ← decodeUIntLE 4 bytes
  let (numberOfLegs, bytes) ← decodeUIntLE 2 bytes
  pure ({ matchId, instrumentId, blockTradeId, blockRfqId, fillQtyMantissa, fillPrice, markPrice, indexPrice, impliedVolatility, takerFlags, numberOfLegs }, bytes)

@[simp] theorem encode_length (message : BlockTradeMessage) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : BlockTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BlockTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BlockTradeMessage

/-- Snapshot Header Message: 24 bytes -/
structure SnapshotHeaderMessage where
  instrumentId : BitVec 64
  incrementalTimestamp : BitVec 64
  incrementalSeqNum : BitVec 64
  deriving DecidableEq, Repr

namespace SnapshotHeaderMessage

def encode (message : SnapshotHeaderMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.incrementalTimestamp
    ++ (encodeUIntLE 8 message.incrementalSeqNum))

def decode (bytes : List UInt8) : Option (SnapshotHeaderMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (incrementalTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (incrementalSeqNum, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, incrementalTimestamp, incrementalSeqNum }, bytes)

@[simp] theorem encode_length (message : SnapshotHeaderMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SnapshotHeaderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotHeaderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SnapshotHeaderMessage

/-- Snapshot Trailer Message: 24 bytes -/
structure SnapshotTrailerMessage where
  instrumentId : BitVec 64
  timestamp : BitVec 64
  incrementSeqNum : BitVec 64
  deriving DecidableEq, Repr

namespace SnapshotTrailerMessage

def encode (message : SnapshotTrailerMessage) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.incrementSeqNum))

def decode (bytes : List UInt8) : Option (SnapshotTrailerMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (incrementSeqNum, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, timestamp, incrementSeqNum }, bytes)

@[simp] theorem encode_length (message : SnapshotTrailerMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SnapshotTrailerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotTrailerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SnapshotTrailerMessage

/-- End Of Cycle Message: 4 bytes -/
structure EndOfCycleMessage where
  activeInstrumentCount : BitVec 32
  deriving DecidableEq, Repr

namespace EndOfCycleMessage

def encode (message : EndOfCycleMessage) : List UInt8 :=
  encodeUIntLE 4 message.activeInstrumentCount

def decode (bytes : List UInt8) : Option (EndOfCycleMessage × List UInt8) := do
  let (activeInstrumentCount, bytes) ← decodeUIntLE 4 bytes
  pure ({ activeInstrumentCount }, bytes)

@[simp] theorem encode_length (message : EndOfCycleMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : EndOfCycleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfCycleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EndOfCycleMessage

/-- Retransmit Request Message: 9 bytes -/
structure RetransmitRequestMessage where
  beginSeqNum : BitVec 64
  messageCountShort : BitVec 8
  deriving DecidableEq, Repr

namespace RetransmitRequestMessage

def encode (message : RetransmitRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.beginSeqNum
    ++ (encodeUInt 1 message.messageCountShort)

def decode (bytes : List UInt8) : Option (RetransmitRequestMessage × List UInt8) := do
  let (beginSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (messageCountShort, bytes) ← decodeUInt 1 bytes
  pure ({ beginSeqNum, messageCountShort }, bytes)

@[simp] theorem encode_length (message : RetransmitRequestMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RetransmitRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RetransmitRequestMessage

/-- Retransmit Reject Message: 49 bytes -/
structure RetransmitRejectMessage where
  retryDelayNanos : BitVec 64
  details : Alpha 40
  reason : BitVec 8
  deriving DecidableEq, Repr

namespace RetransmitRejectMessage

def encode (message : RetransmitRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.retryDelayNanos
    ++ (Alpha.encode message.details
    ++ (encodeUInt 1 message.reason))

def decode (bytes : List UInt8) : Option (RetransmitRejectMessage × List UInt8) := do
  let (retryDelayNanos, bytes) ← decodeUIntLE 8 bytes
  let (details, bytes) ← Alpha.decode 40 bytes
  let (reason, bytes) ← decodeUInt 1 bytes
  pure ({ retryDelayNanos, details, reason }, bytes)

@[simp] theorem encode_length (message : RetransmitRejectMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RetransmitRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RetransmitRejectMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | instrumentMessage (message : InstrumentMessage) -- 10
  | tradingStatusUpdateMessage (message : TradingStatusUpdateMessage) -- 12
  | instrumentInfoMessage (message : InstrumentInfoMessage) -- 13
  | instrumentRefMessage (message : InstrumentRefMessage) -- 14
  | bidPutMessage (message : BidPutMessage) -- 20
  | askPutMessage (message : AskPutMessage) -- 21
  | bidQtyReducedMessage (message : BidQtyReducedMessage) -- 22
  | askQtyReducedMessage (message : AskQtyReducedMessage) -- 23
  | bidDeleteMessage (message : BidDeleteMessage) -- 24
  | askDeleteMessage (message : AskDeleteMessage) -- 25
  | tradeSummaryMessage (message : TradeSummaryMessage) -- 30
  | tradeMessage (message : TradeMessage) -- 31
  | blockTradeMessage (message : BlockTradeMessage) -- 33
  | snapshotHeaderMessage (message : SnapshotHeaderMessage) -- 100
  | snapshotTrailerMessage (message : SnapshotTrailerMessage) -- 101
  | endOfCycleMessage (message : EndOfCycleMessage) -- 119
  | retransmitRequestMessage (message : RetransmitRequestMessage) -- 200
  | retransmitRejectMessage (message : RetransmitRejectMessage) -- 202
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .instrumentMessage _ => 10
  | .tradingStatusUpdateMessage _ => 12
  | .instrumentInfoMessage _ => 13
  | .instrumentRefMessage _ => 14
  | .bidPutMessage _ => 20
  | .askPutMessage _ => 21
  | .bidQtyReducedMessage _ => 22
  | .askQtyReducedMessage _ => 23
  | .bidDeleteMessage _ => 24
  | .askDeleteMessage _ => 25
  | .tradeSummaryMessage _ => 30
  | .tradeMessage _ => 31
  | .blockTradeMessage _ => 33
  | .snapshotHeaderMessage _ => 100
  | .snapshotTrailerMessage _ => 101
  | .endOfCycleMessage _ => 119
  | .retransmitRequestMessage _ => 200
  | .retransmitRejectMessage _ => 202

def encode : Payload → List UInt8
  | .instrumentMessage message => InstrumentMessage.encode message
  | .tradingStatusUpdateMessage message => TradingStatusUpdateMessage.encode message
  | .instrumentInfoMessage message => InstrumentInfoMessage.encode message
  | .instrumentRefMessage message => InstrumentRefMessage.encode message
  | .bidPutMessage message => BidPutMessage.encode message
  | .askPutMessage message => AskPutMessage.encode message
  | .bidQtyReducedMessage message => BidQtyReducedMessage.encode message
  | .askQtyReducedMessage message => AskQtyReducedMessage.encode message
  | .bidDeleteMessage message => BidDeleteMessage.encode message
  | .askDeleteMessage message => AskDeleteMessage.encode message
  | .tradeSummaryMessage message => TradeSummaryMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .blockTradeMessage message => BlockTradeMessage.encode message
  | .snapshotHeaderMessage message => SnapshotHeaderMessage.encode message
  | .snapshotTrailerMessage message => SnapshotTrailerMessage.encode message
  | .endOfCycleMessage message => EndOfCycleMessage.encode message
  | .retransmitRequestMessage message => RetransmitRequestMessage.encode message
  | .retransmitRejectMessage message => RetransmitRejectMessage.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 10 then (InstrumentMessage.decode bytes).map fun (message, rest) => (.instrumentMessage message, rest)
  else if tag = 12 then (TradingStatusUpdateMessage.decode bytes).map fun (message, rest) => (.tradingStatusUpdateMessage message, rest)
  else if tag = 13 then (InstrumentInfoMessage.decode bytes).map fun (message, rest) => (.instrumentInfoMessage message, rest)
  else if tag = 14 then (InstrumentRefMessage.decode bytes).map fun (message, rest) => (.instrumentRefMessage message, rest)
  else if tag = 20 then (BidPutMessage.decode bytes).map fun (message, rest) => (.bidPutMessage message, rest)
  else if tag = 21 then (AskPutMessage.decode bytes).map fun (message, rest) => (.askPutMessage message, rest)
  else if tag = 22 then (BidQtyReducedMessage.decode bytes).map fun (message, rest) => (.bidQtyReducedMessage message, rest)
  else if tag = 23 then (AskQtyReducedMessage.decode bytes).map fun (message, rest) => (.askQtyReducedMessage message, rest)
  else if tag = 24 then (BidDeleteMessage.decode bytes).map fun (message, rest) => (.bidDeleteMessage message, rest)
  else if tag = 25 then (AskDeleteMessage.decode bytes).map fun (message, rest) => (.askDeleteMessage message, rest)
  else if tag = 30 then (TradeSummaryMessage.decode bytes).map fun (message, rest) => (.tradeSummaryMessage message, rest)
  else if tag = 31 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 33 then (BlockTradeMessage.decode bytes).map fun (message, rest) => (.blockTradeMessage message, rest)
  else if tag = 100 then (SnapshotHeaderMessage.decode bytes).map fun (message, rest) => (.snapshotHeaderMessage message, rest)
  else if tag = 101 then (SnapshotTrailerMessage.decode bytes).map fun (message, rest) => (.snapshotTrailerMessage message, rest)
  else if tag = 119 then (EndOfCycleMessage.decode bytes).map fun (message, rest) => (.endOfCycleMessage message, rest)
  else if tag = 200 then (RetransmitRequestMessage.decode bytes).map fun (message, rest) => (.retransmitRequestMessage message, rest)
  else if tag = 202 then (RetransmitRejectMessage.decode bytes).map fun (message, rest) => (.retransmitRejectMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Md Message -/
structure MdMessage where
  schemaVersion : BitVec 16
  messageFlags : BitVec 16
  transactTime : BitVec 64
  payload : Payload
  padding : Capped 65216
  deriving DecidableEq, Repr

namespace MdMessage

def encodeBody (message : MdMessage) : List UInt8 :=
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaVersion
    ++ (encodeUIntLE 2 message.messageFlags
    ++ (encodeUIntLE 8 message.transactTime
    ++ (Payload.encode message.payload
    ++ (message.padding.val)))))

def decodeBody (bytes : List UInt8) : Option MdMessage := do
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaVersion, bytes) ← decodeUIntLE 2 bytes
  let (messageFlags, bytes) ← decodeUIntLE 2 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  let padding_ := bytes
  if fits_padding : padding_.length ≤ 65216 then
    pure { schemaVersion, messageFlags, transactTime, payload, padding := ⟨padding_, fits_padding⟩ }
  else none

theorem decodeBody_encodeBody (message : MdMessage) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.padding.length_le]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : MdMessage) : (encodeBody message).length + 2 < 256 ^ 2 := by
  have bound_padding := message.padding.length_le
  unfold encodeBody
  cases message.payload with
  | instrumentMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentMessage.encode_length]
    omega
  | tradingStatusUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradingStatusUpdateMessage.encode_length]
    omega
  | instrumentInfoMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentInfoMessage.encode_length]
    omega
  | instrumentRefMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentRefMessage.encode_length]
    omega
  | bidPutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, BidPutMessage.encode_length]
    omega
  | askPutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AskPutMessage.encode_length]
    omega
  | bidQtyReducedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, BidQtyReducedMessage.encode_length]
    omega
  | askQtyReducedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AskQtyReducedMessage.encode_length]
    omega
  | bidDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, BidDeleteMessage.encode_length]
    omega
  | askDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AskDeleteMessage.encode_length]
    omega
  | tradeSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeSummaryMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeMessage.encode_length]
    omega
  | blockTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, BlockTradeMessage.encode_length]
    omega
  | snapshotHeaderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SnapshotHeaderMessage.encode_length]
    omega
  | snapshotTrailerMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SnapshotTrailerMessage.encode_length]
    omega
  | endOfCycleMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EndOfCycleMessage.encode_length]
    omega
  | retransmitRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RetransmitRequestMessage.encode_length]
    omega
  | retransmitRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RetransmitRejectMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : MdMessage → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (MdMessage × List UInt8) :=
  decodeFramedAllLE 2 2 decodeBody

@[simp] theorem decode_encode (message : MdMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : MdMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end MdMessage

/-- Packet -/
structure Packet where
  sendingTime : BitVec 64
  seqNum : BitVec 64
  channelId : BitVec 32
  packetType : BitVec 16
  mdMessage : Bounded 2 MdMessage
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 8 message.seqNum
    ++ (encodeUIntLE 4 message.channelId
    ++ (encodeUIntLE 2 message.packetType
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.mdMessage.val.length)
    ++ (encodeMany MdMessage.encode message.mdMessage.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (seqNum, bytes) ← decodeUIntLE 8 bytes
  let (channelId, bytes) ← decodeUIntLE 4 bytes
  let (packetType, bytes) ← decodeUIntLE 2 bytes
  let (messageCount, bytes) ← decodeUIntLE 2 bytes
  let (mdMessage_, bytes) ← decodeMany MdMessage.decode messageCount.toNat bytes
  if fits_mdMessage : mdMessage_.length < 256 ^ 2 then
    pure ({ sendingTime, seqNum, channelId, packetType, mdMessage := ⟨mdMessage_, fits_mdMessage⟩ }, bytes)
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 MdMessage.encode MdMessage.decode MdMessage.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.mdMessage.length_lt]
  rfl

end Packet

end Omi.CoinbaseDeribitMarketdataapiSbeV01
