import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Genium INET Auxiliary Market Data v2.30.7

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNfxfuturesMarketdataGeniumamdV2307

/-- Leg Side: one byte code -/
def LegSide.codes : List UInt8 :=
  [0x42, 0x43]

inductive LegSide where
  | asDefined -- As Defined
  | opposite -- Opposite
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide

def toByte : LegSide → UInt8
  | .asDefined => 0x42
  | .opposite => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide :=
  if byte = 0x42 then .asDefined
  else .opposite

def ofByte (byte : UInt8) : LegSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide) : ofByte value.toByte = value := by
  cases value with
  | asDefined => decide
  | opposite => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSide

/-- Seconds Message: 4 bytes -/
structure SecondsMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace SecondsMessage

def encode (message : SecondsMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (SecondsMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : SecondsMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecondsMessage

/-- Order Book Directory: 135 bytes -/
structure OrderBookDirectory where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  symbol : Alpha 32
  longName : Alpha 32
  isin : Alpha 12
  financialProduct : BitVec 8
  tradingCurrency : Alpha 3
  numberOfDecimalsInPrice : BitVec 16
  numberOfDecimalsInNominalValue : BitVec 16
  oddLotSize : BitVec 32
  roundLotSize : BitVec 32
  blockLotSize : BitVec 32
  nominalValue : BitVec 64
  numberOfLegs : BitVec 8
  underlyingOrderBookId : BitVec 32
  strikePrice : BitVec 32
  expirationDate : BitVec 32
  numberOfDecimalsInStrikePrice : BitVec 16
  putOrCall : BitVec 8
  marketId : BitVec 16
  strategySubtype : BitVec 8
  minimumQuantityAndMultiple : BitVec 32
  deriving DecidableEq, Repr

namespace OrderBookDirectory

def encode (message : OrderBookDirectory) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.longName
    ++ (Alpha.encode message.isin
    ++ (encodeUInt 1 message.financialProduct
    ++ (Alpha.encode message.tradingCurrency
    ++ (encodeUInt 2 message.numberOfDecimalsInPrice
    ++ (encodeUInt 2 message.numberOfDecimalsInNominalValue
    ++ (encodeUInt 4 message.oddLotSize
    ++ (encodeUInt 4 message.roundLotSize
    ++ (encodeUInt 4 message.blockLotSize
    ++ (encodeUInt 8 message.nominalValue
    ++ (encodeUInt 1 message.numberOfLegs
    ++ (encodeUInt 4 message.underlyingOrderBookId
    ++ (encodeUInt 4 message.strikePrice
    ++ (encodeUInt 4 message.expirationDate
    ++ (encodeUInt 2 message.numberOfDecimalsInStrikePrice
    ++ (encodeUInt 1 message.putOrCall
    ++ (encodeUInt 2 message.marketId
    ++ (encodeUInt 1 message.strategySubtype
    ++ (encodeUInt 4 message.minimumQuantityAndMultiple)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderBookDirectory × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 32 bytes
  let (longName, bytes) ← Alpha.decode 32 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (financialProduct, bytes) ← decodeUInt 1 bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (numberOfDecimalsInPrice, bytes) ← decodeUInt 2 bytes
  let (numberOfDecimalsInNominalValue, bytes) ← decodeUInt 2 bytes
  let (oddLotSize, bytes) ← decodeUInt 4 bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (blockLotSize, bytes) ← decodeUInt 4 bytes
  let (nominalValue, bytes) ← decodeUInt 8 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (underlyingOrderBookId, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (expirationDate, bytes) ← decodeUInt 4 bytes
  let (numberOfDecimalsInStrikePrice, bytes) ← decodeUInt 2 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (marketId, bytes) ← decodeUInt 2 bytes
  let (strategySubtype, bytes) ← decodeUInt 1 bytes
  let (minimumQuantityAndMultiple, bytes) ← decodeUInt 4 bytes
  pure ({ timestampNanoseconds, orderBookId, symbol, longName, isin, financialProduct, tradingCurrency, numberOfDecimalsInPrice, numberOfDecimalsInNominalValue, oddLotSize, roundLotSize, blockLotSize, nominalValue, numberOfLegs, underlyingOrderBookId, strikePrice, expirationDate, numberOfDecimalsInStrikePrice, putOrCall, marketId, strategySubtype, minimumQuantityAndMultiple }, bytes)

@[simp] theorem encode_length (message : OrderBookDirectory) : (encode message).length = 135 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderBookDirectory) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookDirectory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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

end OrderBookDirectory

/-- Combination Order Book Leg: 29 bytes -/
structure CombinationOrderBookLeg where
  timestampNanoseconds : BitVec 32
  combinationOrderBookId : BitVec 32
  legOrderBookId : BitVec 32
  legSide : LegSide
  legRatio : BitVec 32
  legPriceFuture : BitVec 32
  legDelta : BitVec 32
  legQuantityFuture : BitVec 32
  deriving DecidableEq, Repr

namespace CombinationOrderBookLeg

def encode (message : CombinationOrderBookLeg) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.combinationOrderBookId
    ++ (encodeUInt 4 message.legOrderBookId
    ++ (LegSide.encode message.legSide
    ++ (encodeUInt 4 message.legRatio
    ++ (encodeUInt 4 message.legPriceFuture
    ++ (encodeUInt 4 message.legDelta
    ++ (encodeUInt 4 message.legQuantityFuture)))))))

def decode (bytes : List UInt8) : Option (CombinationOrderBookLeg × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (combinationOrderBookId, bytes) ← decodeUInt 4 bytes
  let (legOrderBookId, bytes) ← decodeUInt 4 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (legRatio, bytes) ← decodeUInt 4 bytes
  let (legPriceFuture, bytes) ← decodeUInt 4 bytes
  let (legDelta, bytes) ← decodeUInt 4 bytes
  let (legQuantityFuture, bytes) ← decodeUInt 4 bytes
  pure ({ timestampNanoseconds, combinationOrderBookId, legOrderBookId, legSide, legRatio, legPriceFuture, legDelta, legQuantityFuture }, bytes)

@[simp] theorem encode_length (message : CombinationOrderBookLeg) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, LegSide.encode_length]

theorem encode_length_pos (message : CombinationOrderBookLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CombinationOrderBookLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CombinationOrderBookLeg

/-- Tick Size Table Entry: 24 bytes -/
structure TickSizeTableEntry where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  tickSize : BitVec 64
  priceFrom : BitVec 32
  priceTo : BitVec 32
  deriving DecidableEq, Repr

namespace TickSizeTableEntry

def encode (message : TickSizeTableEntry) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.tickSize
    ++ (encodeUInt 4 message.priceFrom
    ++ (encodeUInt 4 message.priceTo))))

def decode (bytes : List UInt8) : Option (TickSizeTableEntry × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (tickSize, bytes) ← decodeUInt 8 bytes
  let (priceFrom, bytes) ← decodeUInt 4 bytes
  let (priceTo, bytes) ← decodeUInt 4 bytes
  pure ({ timestampNanoseconds, orderBookId, tickSize, priceFrom, priceTo }, bytes)

@[simp] theorem encode_length (message : TickSizeTableEntry) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TickSizeTableEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickSizeTableEntry) (rest : List UInt8) :
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

end TickSizeTableEntry

/-- System Event Message: 5 bytes -/
structure SystemEventMessage where
  timestampNanoseconds : BitVec 32
  eventCode : Alpha 1
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (Alpha.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← Alpha.decode 1 bytes
  pure ({ timestampNanoseconds, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Order Book State Message: 28 bytes -/
structure OrderBookStateMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  stateName : Alpha 20
  deriving DecidableEq, Repr

namespace OrderBookStateMessage

def encode (message : OrderBookStateMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (Alpha.encode message.stateName))

def decode (bytes : List UInt8) : Option (OrderBookStateMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (stateName, bytes) ← Alpha.decode 20 bytes
  pure ({ timestampNanoseconds, orderBookId, stateName }, bytes)

@[simp] theorem encode_length (message : OrderBookStateMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderBookStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderBookStateMessage

/-- Reported Trade: 72 bytes -/
structure ReportedTrade where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  tradedQuantity : BitVec 64
  matchId : BitVec 64
  comboGroupId : BitVec 32
  timeOfTradeExecution : BitVec 64
  timeOfTradeAgreement : BitVec 64
  timeOfTradeDissemination : BitVec 64
  tradePrice : BitVec 32
  tradeType : BitVec 16
  reserved : Alpha 7
  secondReserved : Alpha 7
  deriving DecidableEq, Repr

namespace ReportedTrade

def encode (message : ReportedTrade) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.tradedQuantity
    ++ (encodeUInt 8 message.matchId
    ++ (encodeUInt 4 message.comboGroupId
    ++ (encodeUInt 8 message.timeOfTradeExecution
    ++ (encodeUInt 8 message.timeOfTradeAgreement
    ++ (encodeUInt 8 message.timeOfTradeDissemination
    ++ (encodeUInt 4 message.tradePrice
    ++ (encodeUInt 2 message.tradeType
    ++ (Alpha.encode message.reserved
    ++ (Alpha.encode message.secondReserved)))))))))))

def decode (bytes : List UInt8) : Option (ReportedTrade × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (tradedQuantity, bytes) ← decodeUInt 8 bytes
  let (matchId, bytes) ← decodeUInt 8 bytes
  let (comboGroupId, bytes) ← decodeUInt 4 bytes
  let (timeOfTradeExecution, bytes) ← decodeUInt 8 bytes
  let (timeOfTradeAgreement, bytes) ← decodeUInt 8 bytes
  let (timeOfTradeDissemination, bytes) ← decodeUInt 8 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (tradeType, bytes) ← decodeUInt 2 bytes
  let (reserved, bytes) ← Alpha.decode 7 bytes
  let (secondReserved, bytes) ← Alpha.decode 7 bytes
  pure ({ timestampNanoseconds, orderBookId, tradedQuantity, matchId, comboGroupId, timeOfTradeExecution, timeOfTradeAgreement, timeOfTradeDissemination, tradePrice, tradeType, reserved, secondReserved }, bytes)

@[simp] theorem encode_length (message : ReportedTrade) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ReportedTrade) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReportedTrade) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ReportedTrade

/-- Broken Trade Message: 12 bytes -/
structure BrokenTradeMessage where
  timestampNanoseconds : BitVec 32
  matchId : BitVec 64
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 8 message.matchId)

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 8 bytes
  pure ({ timestampNanoseconds, matchId }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BrokenTradeMessage

/-- Open Interest Message: 16 bytes -/
structure OpenInterestMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  openInterest : BitVec 64
  deriving DecidableEq, Repr

namespace OpenInterestMessage

def encode (message : OpenInterestMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.openInterest))

def decode (bytes : List UInt8) : Option (OpenInterestMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (openInterest, bytes) ← decodeUInt 8 bytes
  pure ({ timestampNanoseconds, orderBookId, openInterest }, bytes)

@[simp] theorem encode_length (message : OpenInterestMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OpenInterestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenInterestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpenInterestMessage

/-- Price Message: 13 bytes -/
structure PriceMessage where
  timestampNanoseconds : BitVec 32
  priceType : Alpha 1
  orderBookId : BitVec 32
  price : BitVec 32
  deriving DecidableEq, Repr

namespace PriceMessage

def encode (message : PriceMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (Alpha.encode message.priceType
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 4 message.price)))

def decode (bytes : List UInt8) : Option (PriceMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (priceType, bytes) ← Alpha.decode 1 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ timestampNanoseconds, priceType, orderBookId, price }, bytes)

@[simp] theorem encode_length (message : PriceMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : PriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriceMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | secondsMessage (message : SecondsMessage) -- "T" 0x54
  | orderBookDirectory (message : OrderBookDirectory) -- "R" 0x52
  | combinationOrderBookLeg (message : CombinationOrderBookLeg) -- "M" 0x4D
  | tickSizeTableEntry (message : TickSizeTableEntry) -- "L" 0x4C
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | orderBookStateMessage (message : OrderBookStateMessage) -- "O" 0x4F
  | reportedTrade (message : ReportedTrade) -- "r" 0x72
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  | openInterestMessage (message : OpenInterestMessage) -- "o" 0x6F
  | priceMessage (message : PriceMessage) -- "p" 0x70
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .secondsMessage _ => 84
  | .orderBookDirectory _ => 82
  | .combinationOrderBookLeg _ => 77
  | .tickSizeTableEntry _ => 76
  | .systemEventMessage _ => 83
  | .orderBookStateMessage _ => 79
  | .reportedTrade _ => 114
  | .brokenTradeMessage _ => 66
  | .openInterestMessage _ => 111
  | .priceMessage _ => 112

def encode : Payload → List UInt8
  | .secondsMessage message => SecondsMessage.encode message
  | .orderBookDirectory message => OrderBookDirectory.encode message
  | .combinationOrderBookLeg message => CombinationOrderBookLeg.encode message
  | .tickSizeTableEntry message => TickSizeTableEntry.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .orderBookStateMessage message => OrderBookStateMessage.encode message
  | .reportedTrade message => ReportedTrade.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .openInterestMessage message => OpenInterestMessage.encode message
  | .priceMessage message => PriceMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 135 := by
  cases message with
  | secondsMessage inner =>
    simp only [encode, SecondsMessage.encode_length]
    omega
  | orderBookDirectory inner =>
    simp only [encode, OrderBookDirectory.encode_length]
    omega
  | combinationOrderBookLeg inner =>
    simp only [encode, CombinationOrderBookLeg.encode_length]
    omega
  | tickSizeTableEntry inner =>
    simp only [encode, TickSizeTableEntry.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | orderBookStateMessage inner =>
    simp only [encode, OrderBookStateMessage.encode_length]
    omega
  | reportedTrade inner =>
    simp only [encode, ReportedTrade.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega
  | openInterestMessage inner =>
    simp only [encode, OpenInterestMessage.encode_length]
    omega
  | priceMessage inner =>
    simp only [encode, PriceMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (SecondsMessage.decode bytes).map fun (message, rest) => (.secondsMessage message, rest)
  else if tag = 82 then (OrderBookDirectory.decode bytes).map fun (message, rest) => (.orderBookDirectory message, rest)
  else if tag = 77 then (CombinationOrderBookLeg.decode bytes).map fun (message, rest) => (.combinationOrderBookLeg message, rest)
  else if tag = 76 then (TickSizeTableEntry.decode bytes).map fun (message, rest) => (.tickSizeTableEntry message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 79 then (OrderBookStateMessage.decode bytes).map fun (message, rest) => (.orderBookStateMessage message, rest)
  else if tag = 114 then (ReportedTrade.decode bytes).map fun (message, rest) => (.reportedTrade message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 111 then (OpenInterestMessage.decode bytes).map fun (message, rest) => (.openInterestMessage message, rest)
  else if tag = 112 then (PriceMessage.decode bytes).map fun (message, rest) => (.priceMessage message, rest)
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
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | secondsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecondsMessage.encode_length]
    omega
  | orderBookDirectory inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookDirectory.encode_length]
    omega
  | combinationOrderBookLeg inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CombinationOrderBookLeg.encode_length]
    omega
  | tickSizeTableEntry inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TickSizeTableEntry.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | orderBookStateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookStateMessage.encode_length]
    omega
  | reportedTrade inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReportedTrade.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | openInterestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OpenInterestMessage.encode_length]
    omega
  | priceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PriceMessage.encode_length]
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
  sequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NasdaqNfxfuturesMarketdataGeniumamdV2307
