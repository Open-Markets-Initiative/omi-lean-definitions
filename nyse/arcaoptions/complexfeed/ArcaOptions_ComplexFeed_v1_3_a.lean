import Wire

/-!
# New York Stock Exchange Complex Feed v1.3.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseArcaoptionsComplexfeedXdpV13A

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35]

inductive QuoteCondition where
  | regularTrading -- Regular Trading
  | rotation -- Rotation
  | tradingHalted -- Trading Halted
  | preopen -- Preopen
  | rotationLegalWidthQuotePending -- Rotation Legal Width Quote Pending
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .regularTrading => 0x31
  | .rotation => 0x32
  | .tradingHalted => 0x33
  | .preopen => 0x34
  | .rotationLegalWidthQuotePending => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x31 then .regularTrading
  else if byte = 0x32 then .rotation
  else if byte = 0x33 then .tradingHalted
  else if byte = 0x34 then .preopen
  else .rotationLegalWidthQuotePending

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | regularTrading => decide
  | rotation => decide
  | tradingHalted => decide
  | preopen => decide
  | rotationLegalWidthQuotePending => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : QuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteCondition

/-- Trade Cond 1: one byte code -/
def TradeCond1.codes : List UInt8 :=
  [0x20, 0x49, 0x52, 0x53]

inductive TradeCond1 where
  | regularTrade -- Regular Trade
  | lateReport -- Late Report
  | floorTrade -- Floor Trade
  | soSweepTrade -- So Sweep Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCond1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCond1

def toByte : TradeCond1 → UInt8
  | .regularTrade => 0x20
  | .lateReport => 0x49
  | .floorTrade => 0x52
  | .soSweepTrade => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCond1 :=
  if byte = 0x20 then .regularTrade
  else if byte = 0x49 then .lateReport
  else if byte = 0x52 then .floorTrade
  else .soSweepTrade

def ofByte (byte : UInt8) : TradeCond1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCond1) : ofByte value.toByte = value := by
  cases value with
  | regularTrade => decide
  | lateReport => decide
  | floorTrade => decide
  | soSweepTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCond1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCond1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCond1) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCond1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCond1

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Security Status: one byte code -/
def SecurityStatus.codes : List UInt8 :=
  [0x4C, 0x4E, 0x4F, 0x58, 0x53, 0x55, 0x54, 0x51]

inductive SecurityStatus where
  | lightUpADarkSeries -- Light Up A Dark Series
  | openADarkSeries -- Open A Dark Series
  | open_ -- Open
  | close -- Close
  | halt -- Halt
  | unhalt -- Unhalt
  | unhaltADarkSeries -- Unhalt A Dark Series
  | endOfRfqAuction -- End Of Rfq Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatus

def toByte : SecurityStatus → UInt8
  | .lightUpADarkSeries => 0x4C
  | .openADarkSeries => 0x4E
  | .open_ => 0x4F
  | .close => 0x58
  | .halt => 0x53
  | .unhalt => 0x55
  | .unhaltADarkSeries => 0x54
  | .endOfRfqAuction => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x4C then .lightUpADarkSeries
  else if byte = 0x4E then .openADarkSeries
  else if byte = 0x4F then .open_
  else if byte = 0x58 then .close
  else if byte = 0x53 then .halt
  else if byte = 0x55 then .unhalt
  else if byte = 0x54 then .unhaltADarkSeries
  else .endOfRfqAuction

def ofByte (byte : UInt8) : SecurityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatus) : ofByte value.toByte = value := by
  cases value with
  | lightUpADarkSeries => decide
  | openADarkSeries => decide
  | open_ => decide
  | close => decide
  | halt => decide
  | unhalt => decide
  | unhaltADarkSeries => decide
  | endOfRfqAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityStatus

/-- Leg Security Type: one byte code -/
def LegSecurityType.codes : List UInt8 :=
  [0x4F, 0x45]

inductive LegSecurityType where
  | optionsSeriesLeg -- Options Series Leg
  | equityStockLeg -- Equity Stock Leg
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSecurityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSecurityType

def toByte : LegSecurityType → UInt8
  | .optionsSeriesLeg => 0x4F
  | .equityStockLeg => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSecurityType :=
  if byte = 0x4F then .optionsSeriesLeg
  else .equityStockLeg

def ofByte (byte : UInt8) : LegSecurityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSecurityType) : ofByte value.toByte = value := by
  cases value with
  | optionsSeriesLeg => decide
  | equityStockLeg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSecurityType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSecurityType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSecurityType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegSecurityType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSecurityType

/-- Send Time: 8 bytes -/
structure SendTime where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace SendTime

def encode (message : SendTime) : List UInt8 :=
  encodeUIntLE 4 message.seconds
    ++ (encodeUIntLE 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (SendTime × List UInt8) := do
  let (seconds, bytes) ← decodeUIntLE 4 bytes
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : SendTime) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SendTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SendTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SendTime

/-- Complex Quote Message: 36 bytes -/
structure ComplexQuoteMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  complexIndex : BitVec 32
  symbolSeqNum : BitVec 32
  askPrice : BitVec 32
  bidPrice : BitVec 32
  askVolume : BitVec 16
  bidVolume : BitVec 16
  askCustomerVolume : BitVec 16
  bidCustomerVolume : BitVec 16
  quoteCondition : QuoteCondition
  reserved1 : Alpha 1
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace ComplexQuoteMessage

def encode (message : ComplexQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.complexIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.askPrice
    ++ (encodeUIntLE 4 message.bidPrice
    ++ (encodeUIntLE 2 message.askVolume
    ++ (encodeUIntLE 2 message.bidVolume
    ++ (encodeUIntLE 2 message.askCustomerVolume
    ++ (encodeUIntLE 2 message.bidCustomerVolume
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved2))))))))))))

def decode (bytes : List UInt8) : Option (ComplexQuoteMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (complexIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (askPrice, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 4 bytes
  let (askVolume, bytes) ← decodeUIntLE 2 bytes
  let (bidVolume, bytes) ← decodeUIntLE 2 bytes
  let (askCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (bidCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, complexIndex, symbolSeqNum, askPrice, bidPrice, askVolume, bidVolume, askCustomerVolume, bidCustomerVolume, quoteCondition, reserved1, reserved2 }, bytes)

@[simp] theorem encode_length (message : ComplexQuoteMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, QuoteCondition.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ComplexQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexQuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexQuoteMessage

/-- Complex Trade Message: 32 bytes -/
structure ComplexTradeMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  complexIndex : BitVec 32
  symbolSeqNum : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  volume4 : BitVec 32
  tradeCond1 : TradeCond1
  tradeCond2 : Alpha 1
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace ComplexTradeMessage

def encode (message : ComplexTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.complexIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume4
    ++ (TradeCond1.encode message.tradeCond1
    ++ (Alpha.encode message.tradeCond2
    ++ (Alpha.encode message.reserved2)))))))))

def decode (bytes : List UInt8) : Option (ComplexTradeMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (complexIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume4, bytes) ← decodeUIntLE 4 bytes
  let (tradeCond1, bytes) ← TradeCond1.decode bytes
  let (tradeCond2, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, complexIndex, symbolSeqNum, tradeId, price, volume4, tradeCond1, tradeCond2, reserved2 }, bytes)

@[simp] theorem encode_length (message : ComplexTradeMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCond1.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ComplexTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeCond1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexTradeMessage

/-- Complex Crossing Rfq Message: 24 bytes -/
structure ComplexCrossingRfqMessage where
  sourceTime : BitVec 32
  sourceNs : BitVec 32
  complexIndex : BitVec 32
  symbolSeqNum : BitVec 32
  side : Side
  reserved1 : Alpha 1
  volume2 : BitVec 16
  price : BitVec 32
  deriving DecidableEq, Repr

namespace ComplexCrossingRfqMessage

def encode (message : ComplexCrossingRfqMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceNs
    ++ (encodeUIntLE 4 message.complexIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (Side.encode message.side
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 2 message.volume2
    ++ (encodeUIntLE 4 message.price)))))))

def decode (bytes : List UInt8) : Option (ComplexCrossingRfqMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceNs, bytes) ← decodeUIntLE 4 bytes
  let (complexIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (volume2, bytes) ← decodeUIntLE 2 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTime, sourceNs, complexIndex, symbolSeqNum, side, reserved1, volume2, price }, bytes)

@[simp] theorem encode_length (message : ComplexCrossingRfqMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ComplexCrossingRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexCrossingRfqMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ComplexCrossingRfqMessage

/-- Complex Cube Rfq Message: 24 bytes -/
structure ComplexCubeRfqMessage where
  sourceTime : BitVec 32
  sourceNs : BitVec 32
  complexIndex : BitVec 32
  symbolSeqNum : BitVec 32
  side : Side
  reserved1 : Alpha 1
  volume2 : BitVec 16
  price : BitVec 32
  deriving DecidableEq, Repr

namespace ComplexCubeRfqMessage

def encode (message : ComplexCubeRfqMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceNs
    ++ (encodeUIntLE 4 message.complexIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (Side.encode message.side
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 2 message.volume2
    ++ (encodeUIntLE 4 message.price)))))))

def decode (bytes : List UInt8) : Option (ComplexCubeRfqMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceNs, bytes) ← decodeUIntLE 4 bytes
  let (complexIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (volume2, bytes) ← decodeUIntLE 2 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTime, sourceNs, complexIndex, symbolSeqNum, side, reserved1, volume2, price }, bytes)

@[simp] theorem encode_length (message : ComplexCubeRfqMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ComplexCubeRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexCubeRfqMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ComplexCubeRfqMessage

/-- Complex Status Message: 20 bytes -/
structure ComplexStatusMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  complexIndex : BitVec 32
  symbolSeqNum : BitVec 32
  securityStatus : SecurityStatus
  haltCondition : Alpha 1
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace ComplexStatusMessage

def encode (message : ComplexStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.complexIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (SecurityStatus.encode message.securityStatus
    ++ (Alpha.encode message.haltCondition
    ++ (Alpha.encode message.reserved2))))))

def decode (bytes : List UInt8) : Option (ComplexStatusMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (complexIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (haltCondition, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, complexIndex, symbolSeqNum, securityStatus, haltCondition, reserved2 }, bytes)

@[simp] theorem encode_length (message : ComplexStatusMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ComplexStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexStatusMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexStatusMessage

/-- Refresh Complex Quote Message: 36 bytes -/
structure RefreshComplexQuoteMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  complexIndex : BitVec 32
  symbolSeqNum : BitVec 32
  askPrice : BitVec 32
  bidPrice : BitVec 32
  askVolume : BitVec 16
  bidVolume : BitVec 16
  askCustomerVolume : BitVec 16
  bidCustomerVolume : BitVec 16
  quoteCondition : QuoteCondition
  reserved1 : Alpha 1
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace RefreshComplexQuoteMessage

def encode (message : RefreshComplexQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.complexIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.askPrice
    ++ (encodeUIntLE 4 message.bidPrice
    ++ (encodeUIntLE 2 message.askVolume
    ++ (encodeUIntLE 2 message.bidVolume
    ++ (encodeUIntLE 2 message.askCustomerVolume
    ++ (encodeUIntLE 2 message.bidCustomerVolume
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved2))))))))))))

def decode (bytes : List UInt8) : Option (RefreshComplexQuoteMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (complexIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (askPrice, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 4 bytes
  let (askVolume, bytes) ← decodeUIntLE 2 bytes
  let (bidVolume, bytes) ← decodeUIntLE 2 bytes
  let (askCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (bidCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, complexIndex, symbolSeqNum, askPrice, bidPrice, askVolume, bidVolume, askCustomerVolume, bidCustomerVolume, quoteCondition, reserved1, reserved2 }, bytes)

@[simp] theorem encode_length (message : RefreshComplexQuoteMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, QuoteCondition.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RefreshComplexQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshComplexQuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefreshComplexQuoteMessage

/-- Refresh Complex Trade Message: 32 bytes -/
structure RefreshComplexTradeMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  complexIndex : BitVec 32
  symbolSeqNum : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  volume4 : BitVec 32
  tradeCond1 : TradeCond1
  tradeCond2 : Alpha 1
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace RefreshComplexTradeMessage

def encode (message : RefreshComplexTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.complexIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume4
    ++ (TradeCond1.encode message.tradeCond1
    ++ (Alpha.encode message.tradeCond2
    ++ (Alpha.encode message.reserved2)))))))))

def decode (bytes : List UInt8) : Option (RefreshComplexTradeMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (complexIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume4, bytes) ← decodeUIntLE 4 bytes
  let (tradeCond1, bytes) ← TradeCond1.decode bytes
  let (tradeCond2, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, complexIndex, symbolSeqNum, tradeId, price, volume4, tradeCond1, tradeCond2, reserved2 }, bytes)

@[simp] theorem encode_length (message : RefreshComplexTradeMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCond1.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RefreshComplexTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshComplexTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeCond1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefreshComplexTradeMessage

/-- Leg Definition: 8 bytes -/
structure LegDefinition where
  symbolIndex : BitVec 32
  legRatioQty : BitVec 16
  side : Side
  legSecurityType : LegSecurityType
  deriving DecidableEq, Repr

namespace LegDefinition

def encode (message : LegDefinition) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 2 message.legRatioQty
    ++ (Side.encode message.side
    ++ (LegSecurityType.encode message.legSecurityType)))

def decode (bytes : List UInt8) : Option (LegDefinition × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← Side.decode bytes
  let (legSecurityType, bytes) ← LegSecurityType.decode bytes
  pure ({ symbolIndex, legRatioQty, side, legSecurityType }, bytes)

@[simp] theorem encode_length (message : LegDefinition) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, LegSecurityType.encode_length]

theorem encode_length_pos (message : LegDefinition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegDefinition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [LegSecurityType.decode_encode, some_bind]
  rfl

end LegDefinition

/-- Complex Symbol Definition Message: 44 bytes -/
structure ComplexSymbolDefinitionMessage where
  complexIndex : BitVec 32
  complexSymbol : Alpha 21
  channelId : BitVec 8
  marketId : BitVec 16
  systemId : BitVec 8
  reserved1 : Alpha 1
  streamId : BitVec 16
  noOfLegs : BitVec 16
  reserved2 : Alpha 2
  legDefinition : LegDefinition
  deriving DecidableEq, Repr

namespace ComplexSymbolDefinitionMessage

def encode (message : ComplexSymbolDefinitionMessage) : List UInt8 :=
  encodeUIntLE 4 message.complexIndex
    ++ (Alpha.encode message.complexSymbol
    ++ (encodeUIntLE 1 message.channelId
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUIntLE 1 message.systemId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 2 message.streamId
    ++ (encodeUIntLE 2 message.noOfLegs
    ++ (Alpha.encode message.reserved2
    ++ (LegDefinition.encode message.legDefinition)))))))))

def decode (bytes : List UInt8) : Option (ComplexSymbolDefinitionMessage × List UInt8) := do
  let (complexIndex, bytes) ← decodeUIntLE 4 bytes
  let (complexSymbol, bytes) ← Alpha.decode 21 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (systemId, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (noOfLegs, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (legDefinition, bytes) ← LegDefinition.decode bytes
  pure ({ complexIndex, complexSymbol, channelId, marketId, systemId, reserved1, streamId, noOfLegs, reserved2, legDefinition }, bytes)

@[simp] theorem encode_length (message : ComplexSymbolDefinitionMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LegDefinition.encode_length]

theorem encode_length_pos (message : ComplexSymbolDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexSymbolDefinitionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [LegDefinition.decode_encode, some_bind]
  rfl

end ComplexSymbolDefinitionMessage

/-- Stream Id Message: 4 bytes -/
structure StreamIdMessage where
  streamId : BitVec 16
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace StreamIdMessage

def encode (message : StreamIdMessage) : List UInt8 :=
  encodeUIntLE 2 message.streamId
    ++ (Alpha.encode message.reserved2)

def decode (bytes : List UInt8) : Option (StreamIdMessage × List UInt8) := do
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ streamId, reserved2 }, bytes)

@[simp] theorem encode_length (message : StreamIdMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : StreamIdMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamIdMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StreamIdMessage

/-- Sequence Number Reset Message: 10 bytes -/
structure SequenceNumberResetMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  productId : BitVec 8
  channelId : BitVec 8
  deriving DecidableEq, Repr

namespace SequenceNumberResetMessage

def encode (message : SequenceNumberResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId)))

def decode (bytes : List UInt8) : Option (SequenceNumberResetMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  pure ({ sourceTime, sourceTimeNs, productId, channelId }, bytes)

@[simp] theorem encode_length (message : SequenceNumberResetMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SequenceNumberResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceNumberResetMessage) (rest : List UInt8) :
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

end SequenceNumberResetMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | complexQuoteMessage (message : ComplexQuoteMessage) -- 423
  | complexTradeMessage (message : ComplexTradeMessage) -- 425
  | complexCrossingRfqMessage (message : ComplexCrossingRfqMessage) -- 429
  | complexCubeRfqMessage (message : ComplexCubeRfqMessage) -- 472
  | complexStatusMessage (message : ComplexStatusMessage) -- 433
  | refreshComplexQuoteMessage (message : RefreshComplexQuoteMessage) -- 511
  | refreshComplexTradeMessage (message : RefreshComplexTradeMessage) -- 513
  | complexSymbolDefinitionMessage (message : ComplexSymbolDefinitionMessage) -- 439
  | streamIdMessage (message : StreamIdMessage) -- 455
  | sequenceNumberResetMessage (message : SequenceNumberResetMessage) -- 1
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .complexQuoteMessage _ => 423
  | .complexTradeMessage _ => 425
  | .complexCrossingRfqMessage _ => 429
  | .complexCubeRfqMessage _ => 472
  | .complexStatusMessage _ => 433
  | .refreshComplexQuoteMessage _ => 511
  | .refreshComplexTradeMessage _ => 513
  | .complexSymbolDefinitionMessage _ => 439
  | .streamIdMessage _ => 455
  | .sequenceNumberResetMessage _ => 1

def encode : Payload → List UInt8
  | .complexQuoteMessage message => ComplexQuoteMessage.encode message
  | .complexTradeMessage message => ComplexTradeMessage.encode message
  | .complexCrossingRfqMessage message => ComplexCrossingRfqMessage.encode message
  | .complexCubeRfqMessage message => ComplexCubeRfqMessage.encode message
  | .complexStatusMessage message => ComplexStatusMessage.encode message
  | .refreshComplexQuoteMessage message => RefreshComplexQuoteMessage.encode message
  | .refreshComplexTradeMessage message => RefreshComplexTradeMessage.encode message
  | .complexSymbolDefinitionMessage message => ComplexSymbolDefinitionMessage.encode message
  | .streamIdMessage message => StreamIdMessage.encode message
  | .sequenceNumberResetMessage message => SequenceNumberResetMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 44 := by
  cases message with
  | complexQuoteMessage inner =>
    simp only [encode, ComplexQuoteMessage.encode_length]
    omega
  | complexTradeMessage inner =>
    simp only [encode, ComplexTradeMessage.encode_length]
    omega
  | complexCrossingRfqMessage inner =>
    simp only [encode, ComplexCrossingRfqMessage.encode_length]
    omega
  | complexCubeRfqMessage inner =>
    simp only [encode, ComplexCubeRfqMessage.encode_length]
    omega
  | complexStatusMessage inner =>
    simp only [encode, ComplexStatusMessage.encode_length]
    omega
  | refreshComplexQuoteMessage inner =>
    simp only [encode, RefreshComplexQuoteMessage.encode_length]
    omega
  | refreshComplexTradeMessage inner =>
    simp only [encode, RefreshComplexTradeMessage.encode_length]
    omega
  | complexSymbolDefinitionMessage inner =>
    simp only [encode, ComplexSymbolDefinitionMessage.encode_length]
    omega
  | streamIdMessage inner =>
    simp only [encode, StreamIdMessage.encode_length]
    omega
  | sequenceNumberResetMessage inner =>
    simp only [encode, SequenceNumberResetMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 423 then (ComplexQuoteMessage.decode bytes).map fun (message, rest) => (.complexQuoteMessage message, rest)
  else if tag = 425 then (ComplexTradeMessage.decode bytes).map fun (message, rest) => (.complexTradeMessage message, rest)
  else if tag = 429 then (ComplexCrossingRfqMessage.decode bytes).map fun (message, rest) => (.complexCrossingRfqMessage message, rest)
  else if tag = 472 then (ComplexCubeRfqMessage.decode bytes).map fun (message, rest) => (.complexCubeRfqMessage message, rest)
  else if tag = 433 then (ComplexStatusMessage.decode bytes).map fun (message, rest) => (.complexStatusMessage message, rest)
  else if tag = 511 then (RefreshComplexQuoteMessage.decode bytes).map fun (message, rest) => (.refreshComplexQuoteMessage message, rest)
  else if tag = 513 then (RefreshComplexTradeMessage.decode bytes).map fun (message, rest) => (.refreshComplexTradeMessage message, rest)
  else if tag = 439 then (ComplexSymbolDefinitionMessage.decode bytes).map fun (message, rest) => (.complexSymbolDefinitionMessage message, rest)
  else if tag = 455 then (StreamIdMessage.decode bytes).map fun (message, rest) => (.streamIdMessage message, rest)
  else if tag = 1 then (SequenceNumberResetMessage.decode bytes).map fun (message, rest) => (.sequenceNumberResetMessage message, rest)
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
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | complexQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ComplexQuoteMessage.encode_length]
    omega
  | complexTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ComplexTradeMessage.encode_length]
    omega
  | complexCrossingRfqMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ComplexCrossingRfqMessage.encode_length]
    omega
  | complexCubeRfqMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ComplexCubeRfqMessage.encode_length]
    omega
  | complexStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ComplexStatusMessage.encode_length]
    omega
  | refreshComplexQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RefreshComplexQuoteMessage.encode_length]
    omega
  | refreshComplexTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RefreshComplexTradeMessage.encode_length]
    omega
  | complexSymbolDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ComplexSymbolDefinitionMessage.encode_length]
    omega
  | streamIdMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, StreamIdMessage.encode_length]
    omega
  | sequenceNumberResetMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SequenceNumberResetMessage.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  packetSize : BitVec 16
  deliveryFlag : BitVec 8
  sequenceNumber : BitVec 32
  sendTime : SendTime
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.packetSize
    ++ (encodeUIntLE 1 message.deliveryFlag
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (SendTime.encode message.sendTime
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (packetSize, bytes) ← decodeUIntLE 2 bytes
  let (deliveryFlag, bytes) ← decodeUIntLE 1 bytes
  let (messageCount, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← SendTime.decode bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ packetSize, deliveryFlag, sequenceNumber, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
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
  rw [List.append_assoc, SendTime.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NyseArcaoptionsComplexfeedXdpV13A
