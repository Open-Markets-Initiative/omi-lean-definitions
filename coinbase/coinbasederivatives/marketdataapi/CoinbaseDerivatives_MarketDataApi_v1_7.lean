import Omi.Wire

/-!
# Coinbase Market Data Api v1.7

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Packet Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Definition Flags is a bit field set, proven as its 2 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CoinbaseCoinbasederivativesMarketdataapiSbeV17

/-- Stat Type: one byte code -/
def StatType.codes : List UInt8 :=
  [0x34, 0x35, 0x36, 0x37, 0x38, 0x46, 0x49]

inductive StatType where
  | dayOpeningPrice -- Day Opening Price
  | closingPrice -- Closing Price
  | settlementPrice -- Settlement Price
  | tradingSessionHighPrice -- Trading Session High Price
  | tradingSessionLowPrice -- Trading Session Low Price
  | referencePrice -- Reference Price
  | indicativeOpeningPrice -- Indicative Opening Price
  | unlisted (byte : { byte : UInt8 // byte ∉ StatType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StatType

def toByte : StatType → UInt8
  | .dayOpeningPrice => 0x34
  | .closingPrice => 0x35
  | .settlementPrice => 0x36
  | .tradingSessionHighPrice => 0x37
  | .tradingSessionLowPrice => 0x38
  | .referencePrice => 0x46
  | .indicativeOpeningPrice => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StatType :=
  if byte = 0x34 then .dayOpeningPrice
  else if byte = 0x35 then .closingPrice
  else if byte = 0x36 then .settlementPrice
  else if byte = 0x37 then .tradingSessionHighPrice
  else if byte = 0x38 then .tradingSessionLowPrice
  else if byte = 0x46 then .referencePrice
  else .indicativeOpeningPrice

def ofByte (byte : UInt8) : StatType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StatType) : ofByte value.toByte = value := by
  cases value with
  | dayOpeningPrice => decide
  | closingPrice => decide
  | settlementPrice => decide
  | tradingSessionHighPrice => decide
  | tradingSessionLowPrice => decide
  | referencePrice => decide
  | indicativeOpeningPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StatType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StatType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StatType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StatType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StatType

/-- Packet Header: 24 bytes -/
structure PacketHeader where
  sendingTime : BitVec 64
  seqNum : BitVec 64
  channelId : BitVec 16
  packetFlags : BitVec 8
  messageCount : BitVec 8
  snapshotInstrumentId : BitVec 32
  deriving DecidableEq, Repr

namespace PacketHeader

def encode (message : PacketHeader) : List UInt8 :=
  encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 8 message.seqNum
    ++ (encodeUIntLE 2 message.channelId
    ++ (encodeUIntLE 1 message.packetFlags
    ++ (encodeUInt 1 message.messageCount
    ++ (encodeUIntLE 4 message.snapshotInstrumentId)))))

def decode (bytes : List UInt8) : Option (PacketHeader × List UInt8) := do
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (seqNum, bytes) ← decodeUIntLE 8 bytes
  let (channelId, bytes) ← decodeUIntLE 2 bytes
  let (packetFlags, bytes) ← decodeUIntLE 1 bytes
  let (messageCount, bytes) ← decodeUInt 1 bytes
  let (snapshotInstrumentId, bytes) ← decodeUIntLE 4 bytes
  pure ({ sendingTime, seqNum, channelId, packetFlags, messageCount, snapshotInstrumentId }, bytes)

@[simp] theorem encode_length (message : PacketHeader) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : PacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PacketHeader) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end PacketHeader

/-- Instr Header: 22 bytes -/
structure InstrHeader where
  instrumentFlags : BitVec 8
  instrumentSide : BitVec 8
  instrumentId : BitVec 32
  instrSeqNum : BitVec 32
  tradingSessionDate : BitVec 16
  reserved : BitVec 16
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace InstrHeader

def encode (message : InstrHeader) : List UInt8 :=
  encodeUInt 1 message.instrumentFlags
    ++ (encodeUInt 1 message.instrumentSide
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 4 message.instrSeqNum
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (encodeUIntLE 2 message.reserved
    ++ (encodeUIntLE 8 message.transactTime))))))

def decode (bytes : List UInt8) : Option (InstrHeader × List UInt8) := do
  let (instrumentFlags, bytes) ← decodeUInt 1 bytes
  let (instrumentSide, bytes) ← decodeUInt 1 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (instrSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (reserved, bytes) ← decodeUIntLE 2 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentFlags, instrumentSide, instrumentId, instrSeqNum, tradingSessionDate, reserved, transactTime }, bytes)

@[simp] theorem encode_length (message : InstrHeader) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : InstrHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

end InstrHeader

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

/-- Outright Instrument Definition Message: 174 bytes -/
structure OutrightInstrumentDefinitionMessage where
  instrHeader : InstrHeader
  symbol : Alpha 24
  productCode : Alpha 8
  description : Alpha 32
  tickSize : BitVec 64
  cfiCode : Alpha 8
  currency : Alpha 8
  firstTradingSessionDate : BitVec 16
  lastTradingSessionDate : BitVec 16
  oldContractSize : BitVec 32
  priorSettlementPriceOptional : BitVec 64
  settlementPrice : BitVec 64
  limitDownPrice : BitVec 64
  limitUpPrice : BitVec 64
  productId : BitVec 32
  productGroup : BitVec 8
  tradingStatus : BitVec 8
  definitionFlags : BitVec 16
  contractSize : BitVec 64
  logicalExpiry : LogicalExpiry
  deriving DecidableEq, Repr

namespace OutrightInstrumentDefinitionMessage

def encode (message : OutrightInstrumentDefinitionMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.description
    ++ (encodeUIntLE 8 message.tickSize
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 2 message.firstTradingSessionDate
    ++ (encodeUIntLE 2 message.lastTradingSessionDate
    ++ (encodeUIntLE 4 message.oldContractSize
    ++ (encodeUIntLE 8 message.priorSettlementPriceOptional
    ++ (encodeUIntLE 8 message.settlementPrice
    ++ (encodeUIntLE 8 message.limitDownPrice
    ++ (encodeUIntLE 8 message.limitUpPrice
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUInt 1 message.productGroup
    ++ (encodeUInt 1 message.tradingStatus
    ++ (encodeUIntLE 2 message.definitionFlags
    ++ (encodeUIntLE 8 message.contractSize
    ++ (LogicalExpiry.encode message.logicalExpiry)))))))))))))))))))

def decode (bytes : List UInt8) : Option (OutrightInstrumentDefinitionMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (symbol, bytes) ← Alpha.decode 24 bytes
  let (productCode, bytes) ← Alpha.decode 8 bytes
  let (description, bytes) ← Alpha.decode 32 bytes
  let (tickSize, bytes) ← decodeUIntLE 8 bytes
  let (cfiCode, bytes) ← Alpha.decode 8 bytes
  let (currency, bytes) ← Alpha.decode 8 bytes
  let (firstTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (lastTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (oldContractSize, bytes) ← decodeUIntLE 4 bytes
  let (priorSettlementPriceOptional, bytes) ← decodeUIntLE 8 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (limitDownPrice, bytes) ← decodeUIntLE 8 bytes
  let (limitUpPrice, bytes) ← decodeUIntLE 8 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (productGroup, bytes) ← decodeUInt 1 bytes
  let (tradingStatus, bytes) ← decodeUInt 1 bytes
  let (definitionFlags, bytes) ← decodeUIntLE 2 bytes
  let (contractSize, bytes) ← decodeUIntLE 8 bytes
  let (logicalExpiry, bytes) ← LogicalExpiry.decode bytes
  pure ({ instrHeader, symbol, productCode, description, tickSize, cfiCode, currency, firstTradingSessionDate, lastTradingSessionDate, oldContractSize, priorSettlementPriceOptional, settlementPrice, limitDownPrice, limitUpPrice, productId, productGroup, tradingStatus, definitionFlags, contractSize, logicalExpiry }, bytes)

@[simp] theorem encode_length (message : OutrightInstrumentDefinitionMessage) : (encode message).length = 174 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length, LogicalExpiry.encode_length]

theorem encode_length_pos (message : OutrightInstrumentDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightInstrumentDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [LogicalExpiry.decode_encode, some_bind]
  rfl

end OutrightInstrumentDefinitionMessage

/-- Spread Instrument Definition Message: 175 bytes -/
structure SpreadInstrumentDefinitionMessage where
  instrHeader : InstrHeader
  symbol : Alpha 24
  productCode : Alpha 8
  description : Alpha 32
  tickSize : BitVec 64
  cfiCode : Alpha 8
  currency : Alpha 8
  firstTradingSessionDate : BitVec 16
  lastTradingSessionDate : BitVec 16
  oldContractSize : BitVec 32
  priorSettlementPriceOptional : BitVec 64
  settlementPrice : BitVec 64
  limitDownPrice : BitVec 64
  limitUpPrice : BitVec 64
  productId : BitVec 32
  productGroup : BitVec 8
  tradingStatus : BitVec 8
  leg1InstrumentId : BitVec 32
  leg2InstrumentId : BitVec 32
  spreadBuyConvention : BitVec 8
  definitionFlags : BitVec 16
  logicalExpiry : LogicalExpiry
  deriving DecidableEq, Repr

namespace SpreadInstrumentDefinitionMessage

def encode (message : SpreadInstrumentDefinitionMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.description
    ++ (encodeUIntLE 8 message.tickSize
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 2 message.firstTradingSessionDate
    ++ (encodeUIntLE 2 message.lastTradingSessionDate
    ++ (encodeUIntLE 4 message.oldContractSize
    ++ (encodeUIntLE 8 message.priorSettlementPriceOptional
    ++ (encodeUIntLE 8 message.settlementPrice
    ++ (encodeUIntLE 8 message.limitDownPrice
    ++ (encodeUIntLE 8 message.limitUpPrice
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUInt 1 message.productGroup
    ++ (encodeUInt 1 message.tradingStatus
    ++ (encodeUIntLE 4 message.leg1InstrumentId
    ++ (encodeUIntLE 4 message.leg2InstrumentId
    ++ (encodeUInt 1 message.spreadBuyConvention
    ++ (encodeUIntLE 2 message.definitionFlags
    ++ (LogicalExpiry.encode message.logicalExpiry)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SpreadInstrumentDefinitionMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (symbol, bytes) ← Alpha.decode 24 bytes
  let (productCode, bytes) ← Alpha.decode 8 bytes
  let (description, bytes) ← Alpha.decode 32 bytes
  let (tickSize, bytes) ← decodeUIntLE 8 bytes
  let (cfiCode, bytes) ← Alpha.decode 8 bytes
  let (currency, bytes) ← Alpha.decode 8 bytes
  let (firstTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (lastTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (oldContractSize, bytes) ← decodeUIntLE 4 bytes
  let (priorSettlementPriceOptional, bytes) ← decodeUIntLE 8 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (limitDownPrice, bytes) ← decodeUIntLE 8 bytes
  let (limitUpPrice, bytes) ← decodeUIntLE 8 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (productGroup, bytes) ← decodeUInt 1 bytes
  let (tradingStatus, bytes) ← decodeUInt 1 bytes
  let (leg1InstrumentId, bytes) ← decodeUIntLE 4 bytes
  let (leg2InstrumentId, bytes) ← decodeUIntLE 4 bytes
  let (spreadBuyConvention, bytes) ← decodeUInt 1 bytes
  let (definitionFlags, bytes) ← decodeUIntLE 2 bytes
  let (logicalExpiry, bytes) ← LogicalExpiry.decode bytes
  pure ({ instrHeader, symbol, productCode, description, tickSize, cfiCode, currency, firstTradingSessionDate, lastTradingSessionDate, oldContractSize, priorSettlementPriceOptional, settlementPrice, limitDownPrice, limitUpPrice, productId, productGroup, tradingStatus, leg1InstrumentId, leg2InstrumentId, spreadBuyConvention, definitionFlags, logicalExpiry }, bytes)

@[simp] theorem encode_length (message : SpreadInstrumentDefinitionMessage) : (encode message).length = 175 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length, LogicalExpiry.encode_length]

theorem encode_length_pos (message : SpreadInstrumentDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadInstrumentDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [LogicalExpiry.decode_encode, some_bind]
  rfl

end SpreadInstrumentDefinitionMessage

/-- Option Instrument Definition Message: 167 bytes -/
structure OptionInstrumentDefinitionMessage where
  instrHeader : InstrHeader
  symbol : Alpha 24
  productCode : Alpha 8
  description : Alpha 32
  smallTick : BitVec 64
  cfiCode : Alpha 8
  largeTick : BitVec 64
  largeTickThreshold : BitVec 64
  strikePrice : BitVec 64
  firstTradingSessionDate : BitVec 16
  lastTradingSessionDate : BitVec 16
  priorSettlementPrice : BitVec 64
  settlementPrice : BitVec 64
  productId : BitVec 32
  underlyingInstrumentId : BitVec 32
  productGroup : BitVec 8
  tradingStatus : BitVec 8
  definitionFlags : BitVec 16
  optionExpiryType : BitVec 8
  logicalExpiry : LogicalExpiry
  deriving DecidableEq, Repr

namespace OptionInstrumentDefinitionMessage

def encode (message : OptionInstrumentDefinitionMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.description
    ++ (encodeUIntLE 8 message.smallTick
    ++ (Alpha.encode message.cfiCode
    ++ (encodeUIntLE 8 message.largeTick
    ++ (encodeUIntLE 8 message.largeTickThreshold
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 2 message.firstTradingSessionDate
    ++ (encodeUIntLE 2 message.lastTradingSessionDate
    ++ (encodeUIntLE 8 message.priorSettlementPrice
    ++ (encodeUIntLE 8 message.settlementPrice
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.underlyingInstrumentId
    ++ (encodeUInt 1 message.productGroup
    ++ (encodeUInt 1 message.tradingStatus
    ++ (encodeUIntLE 2 message.definitionFlags
    ++ (encodeUInt 1 message.optionExpiryType
    ++ (LogicalExpiry.encode message.logicalExpiry)))))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionInstrumentDefinitionMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (symbol, bytes) ← Alpha.decode 24 bytes
  let (productCode, bytes) ← Alpha.decode 8 bytes
  let (description, bytes) ← Alpha.decode 32 bytes
  let (smallTick, bytes) ← decodeUIntLE 8 bytes
  let (cfiCode, bytes) ← Alpha.decode 8 bytes
  let (largeTick, bytes) ← decodeUIntLE 8 bytes
  let (largeTickThreshold, bytes) ← decodeUIntLE 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (firstTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (lastTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (priorSettlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingInstrumentId, bytes) ← decodeUIntLE 4 bytes
  let (productGroup, bytes) ← decodeUInt 1 bytes
  let (tradingStatus, bytes) ← decodeUInt 1 bytes
  let (definitionFlags, bytes) ← decodeUIntLE 2 bytes
  let (optionExpiryType, bytes) ← decodeUInt 1 bytes
  let (logicalExpiry, bytes) ← LogicalExpiry.decode bytes
  pure ({ instrHeader, symbol, productCode, description, smallTick, cfiCode, largeTick, largeTickThreshold, strikePrice, firstTradingSessionDate, lastTradingSessionDate, priorSettlementPrice, settlementPrice, productId, underlyingInstrumentId, productGroup, tradingStatus, definitionFlags, optionExpiryType, logicalExpiry }, bytes)

@[simp] theorem encode_length (message : OptionInstrumentDefinitionMessage) : (encode message).length = 167 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length, LogicalExpiry.encode_length]

theorem encode_length_pos (message : OptionInstrumentDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionInstrumentDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [LogicalExpiry.decode_encode, some_bind]
  rfl

end OptionInstrumentDefinitionMessage

/-- Trading Status Update Message: 39 bytes -/
structure TradingStatusUpdateMessage where
  instrHeader : InstrHeader
  limitDownPrice : BitVec 64
  limitUpPrice : BitVec 64
  tradingStatus : BitVec 8
  deriving DecidableEq, Repr

namespace TradingStatusUpdateMessage

def encode (message : TradingStatusUpdateMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (encodeUIntLE 8 message.limitDownPrice
    ++ (encodeUIntLE 8 message.limitUpPrice
    ++ (encodeUInt 1 message.tradingStatus)))

def decode (bytes : List UInt8) : Option (TradingStatusUpdateMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (limitDownPrice, bytes) ← decodeUIntLE 8 bytes
  let (limitUpPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradingStatus, bytes) ← decodeUInt 1 bytes
  pure ({ instrHeader, limitDownPrice, limitUpPrice, tradingStatus }, bytes)

@[simp] theorem encode_length (message : TradingStatusUpdateMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TradingStatusUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingStatusUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradingStatusUpdateMessage

/-- Order Put Message: 42 bytes -/
structure OrderPutMessage where
  instrHeader : InstrHeader
  orderId : BitVec 64
  price : BitVec 64
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace OrderPutMessage

def encode (message : OrderPutMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity)))

def decode (bytes : List UInt8) : Option (OrderPutMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrHeader, orderId, price, quantity }, bytes)

@[simp] theorem encode_length (message : OrderPutMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderPutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderPutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderPutMessage

/-- Order Delete Message: 30 bytes -/
structure OrderDeleteMessage where
  instrHeader : InstrHeader
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (encodeUIntLE 8 message.orderId)

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrHeader, orderId }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderDeleteMessage

/-- Implied Order Update Message: 46 bytes -/
structure ImpliedOrderUpdateMessage where
  instrHeader : InstrHeader
  bestPrice : BitVec 64
  nextPrice : BitVec 64
  bestQty : BitVec 32
  nextQty : BitVec 32
  deriving DecidableEq, Repr

namespace ImpliedOrderUpdateMessage

def encode (message : ImpliedOrderUpdateMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (encodeUIntLE 8 message.bestPrice
    ++ (encodeUIntLE 8 message.nextPrice
    ++ (encodeUIntLE 4 message.bestQty
    ++ (encodeUIntLE 4 message.nextQty))))

def decode (bytes : List UInt8) : Option (ImpliedOrderUpdateMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (bestPrice, bytes) ← decodeUIntLE 8 bytes
  let (nextPrice, bytes) ← decodeUIntLE 8 bytes
  let (bestQty, bytes) ← decodeUIntLE 4 bytes
  let (nextQty, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrHeader, bestPrice, nextPrice, bestQty, nextQty }, bytes)

@[simp] theorem encode_length (message : ImpliedOrderUpdateMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : ImpliedOrderUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImpliedOrderUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ImpliedOrderUpdateMessage

/-- Trade Summary Message: 58 bytes -/
structure TradeSummaryMessage where
  instrHeader : InstrHeader
  aggressorOrderId : BitVec 64
  aggressorReceiveTime : BitVec 64
  vwapPrice : BitVec 64
  deepestPrice : BitVec 64
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace TradeSummaryMessage

def encode (message : TradeSummaryMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (encodeUIntLE 8 message.aggressorOrderId
    ++ (encodeUIntLE 8 message.aggressorReceiveTime
    ++ (encodeUIntLE 8 message.vwapPrice
    ++ (encodeUIntLE 8 message.deepestPrice
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (TradeSummaryMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (aggressorOrderId, bytes) ← decodeUIntLE 8 bytes
  let (aggressorReceiveTime, bytes) ← decodeUIntLE 8 bytes
  let (vwapPrice, bytes) ← decodeUIntLE 8 bytes
  let (deepestPrice, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrHeader, aggressorOrderId, aggressorReceiveTime, vwapPrice, deepestPrice, quantity }, bytes)

@[simp] theorem encode_length (message : TradeSummaryMessage) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
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

end TradeSummaryMessage

/-- Trade Message: 58 bytes -/
structure TradeMessage where
  instrHeader : InstrHeader
  matchId : BitVec 64
  buyOrderId : BitVec 64
  sellOrderId : BitVec 64
  price : BitVec 64
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.buyOrderId
    ++ (encodeUIntLE 8 message.sellOrderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (buyOrderId, bytes) ← decodeUIntLE 8 bytes
  let (sellOrderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrHeader, matchId, buyOrderId, sellOrderId, price, quantity }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
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

/-- Trade Amend Message: 62 bytes -/
structure TradeAmendMessage where
  instrHeader : InstrHeader
  matchId : BitVec 64
  buyOrderId : BitVec 64
  sellOrderId : BitVec 64
  oldPrice : BitVec 64
  newPrice : BitVec 64
  deriving DecidableEq, Repr

namespace TradeAmendMessage

def encode (message : TradeAmendMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.buyOrderId
    ++ (encodeUIntLE 8 message.sellOrderId
    ++ (encodeUIntLE 8 message.oldPrice
    ++ (encodeUIntLE 8 message.newPrice)))))

def decode (bytes : List UInt8) : Option (TradeAmendMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (buyOrderId, bytes) ← decodeUIntLE 8 bytes
  let (sellOrderId, bytes) ← decodeUIntLE 8 bytes
  let (oldPrice, bytes) ← decodeUIntLE 8 bytes
  let (newPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrHeader, matchId, buyOrderId, sellOrderId, oldPrice, newPrice }, bytes)

@[simp] theorem encode_length (message : TradeAmendMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeAmendMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeAmendMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
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

end TradeAmendMessage

/-- Spread Trade Amend Message: 94 bytes -/
structure SpreadTradeAmendMessage where
  instrHeader : InstrHeader
  matchId : BitVec 64
  buyOrderId : BitVec 64
  sellOrderId : BitVec 64
  oldPrice : BitVec 64
  newPrice : BitVec 64
  oldLeg1Price : BitVec 64
  newLeg1Price : BitVec 64
  oldLeg2Price : BitVec 64
  newLeg2Price : BitVec 64
  deriving DecidableEq, Repr

namespace SpreadTradeAmendMessage

def encode (message : SpreadTradeAmendMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.buyOrderId
    ++ (encodeUIntLE 8 message.sellOrderId
    ++ (encodeUIntLE 8 message.oldPrice
    ++ (encodeUIntLE 8 message.newPrice
    ++ (encodeUIntLE 8 message.oldLeg1Price
    ++ (encodeUIntLE 8 message.newLeg1Price
    ++ (encodeUIntLE 8 message.oldLeg2Price
    ++ (encodeUIntLE 8 message.newLeg2Price)))))))))

def decode (bytes : List UInt8) : Option (SpreadTradeAmendMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (buyOrderId, bytes) ← decodeUIntLE 8 bytes
  let (sellOrderId, bytes) ← decodeUIntLE 8 bytes
  let (oldPrice, bytes) ← decodeUIntLE 8 bytes
  let (newPrice, bytes) ← decodeUIntLE 8 bytes
  let (oldLeg1Price, bytes) ← decodeUIntLE 8 bytes
  let (newLeg1Price, bytes) ← decodeUIntLE 8 bytes
  let (oldLeg2Price, bytes) ← decodeUIntLE 8 bytes
  let (newLeg2Price, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrHeader, matchId, buyOrderId, sellOrderId, oldPrice, newPrice, oldLeg1Price, newLeg1Price, oldLeg2Price, newLeg2Price }, bytes)

@[simp] theorem encode_length (message : SpreadTradeAmendMessage) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SpreadTradeAmendMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadTradeAmendMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SpreadTradeAmendMessage

/-- Trade Bust Message: 46 bytes -/
structure TradeBustMessage where
  instrHeader : InstrHeader
  matchId : BitVec 64
  buyOrderId : BitVec 64
  sellOrderId : BitVec 64
  deriving DecidableEq, Repr

namespace TradeBustMessage

def encode (message : TradeBustMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.buyOrderId
    ++ (encodeUIntLE 8 message.sellOrderId)))

def decode (bytes : List UInt8) : Option (TradeBustMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (buyOrderId, bytes) ← decodeUIntLE 8 bytes
  let (sellOrderId, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrHeader, matchId, buyOrderId, sellOrderId }, bytes)

@[simp] theorem encode_length (message : TradeBustMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeBustMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeBustMessage

/-- Market Stat Message: 31 bytes -/
structure MarketStatMessage where
  instrHeader : InstrHeader
  price : BitVec 64
  statType : StatType
  deriving DecidableEq, Repr

namespace MarketStatMessage

def encode (message : MarketStatMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (encodeUIntLE 8 message.price
    ++ (StatType.encode message.statType))

def decode (bytes : List UInt8) : Option (MarketStatMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (statType, bytes) ← StatType.decode bytes
  pure ({ instrHeader, price, statType }, bytes)

@[simp] theorem encode_length (message : MarketStatMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, encodeUIntLE_length, StatType.encode_length]

theorem encode_length_pos (message : MarketStatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [StatType.decode_encode, some_bind]
  rfl

end MarketStatMessage

/-- Trade Session Volume Message: 34 bytes -/
structure TradeSessionVolumeMessage where
  instrHeader : InstrHeader
  vwapPrice : BitVec 64
  tradeVolume : BitVec 32
  deriving DecidableEq, Repr

namespace TradeSessionVolumeMessage

def encode (message : TradeSessionVolumeMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (encodeUIntLE 8 message.vwapPrice
    ++ (encodeUIntLE 4 message.tradeVolume))

def decode (bytes : List UInt8) : Option (TradeSessionVolumeMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (vwapPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradeVolume, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrHeader, vwapPrice, tradeVolume }, bytes)

@[simp] theorem encode_length (message : TradeSessionVolumeMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeSessionVolumeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeSessionVolumeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeSessionVolumeMessage

/-- Open Interest Message: 26 bytes -/
structure OpenInterestMessage where
  instrHeader : InstrHeader
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace OpenInterestMessage

def encode (message : OpenInterestMessage) : List UInt8 :=
  InstrHeader.encode message.instrHeader
    ++ (encodeUIntLE 4 message.quantity)

def decode (bytes : List UInt8) : Option (OpenInterestMessage × List UInt8) := do
  let (instrHeader, bytes) ← InstrHeader.decode bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrHeader, quantity }, bytes)

@[simp] theorem encode_length (message : OpenInterestMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, InstrHeader.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OpenInterestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenInterestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InstrHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OpenInterestMessage

/-- Start Of Outright Instrument Snapshot Message: 130 bytes -/
structure StartOfOutrightInstrumentSnapshotMessage where
  snapshotSeqNum : BitVec 16
  lastInstrSeqNum : BitVec 32
  symbol : Alpha 24
  productCode : Alpha 8
  description : Alpha 32
  tickSize : BitVec 64
  cfiCode : Alpha 8
  currency : Alpha 8
  productId : BitVec 32
  oldContractSize : BitVec 32
  orderCount : BitVec 32
  firstTradingSessionDate : BitVec 16
  lastTradingSessionDate : BitVec 16
  tradingSessionDate : BitVec 16
  productGroup : BitVec 8
  tradingStatus : BitVec 8
  contractSize : BitVec 64
  logicalExpiry : LogicalExpiry
  deriving DecidableEq, Repr

namespace StartOfOutrightInstrumentSnapshotMessage

def encode (message : StartOfOutrightInstrumentSnapshotMessage) : List UInt8 :=
  encodeUIntLE 2 message.snapshotSeqNum
    ++ (encodeUIntLE 4 message.lastInstrSeqNum
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.description
    ++ (encodeUIntLE 8 message.tickSize
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.oldContractSize
    ++ (encodeUIntLE 4 message.orderCount
    ++ (encodeUIntLE 2 message.firstTradingSessionDate
    ++ (encodeUIntLE 2 message.lastTradingSessionDate
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (encodeUInt 1 message.productGroup
    ++ (encodeUInt 1 message.tradingStatus
    ++ (encodeUIntLE 8 message.contractSize
    ++ (LogicalExpiry.encode message.logicalExpiry)))))))))))))))))

def decode (bytes : List UInt8) : Option (StartOfOutrightInstrumentSnapshotMessage × List UInt8) := do
  let (snapshotSeqNum, bytes) ← decodeUIntLE 2 bytes
  let (lastInstrSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 24 bytes
  let (productCode, bytes) ← Alpha.decode 8 bytes
  let (description, bytes) ← Alpha.decode 32 bytes
  let (tickSize, bytes) ← decodeUIntLE 8 bytes
  let (cfiCode, bytes) ← Alpha.decode 8 bytes
  let (currency, bytes) ← Alpha.decode 8 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (oldContractSize, bytes) ← decodeUIntLE 4 bytes
  let (orderCount, bytes) ← decodeUIntLE 4 bytes
  let (firstTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (lastTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (productGroup, bytes) ← decodeUInt 1 bytes
  let (tradingStatus, bytes) ← decodeUInt 1 bytes
  let (contractSize, bytes) ← decodeUIntLE 8 bytes
  let (logicalExpiry, bytes) ← LogicalExpiry.decode bytes
  pure ({ snapshotSeqNum, lastInstrSeqNum, symbol, productCode, description, tickSize, cfiCode, currency, productId, oldContractSize, orderCount, firstTradingSessionDate, lastTradingSessionDate, tradingSessionDate, productGroup, tradingStatus, contractSize, logicalExpiry }, bytes)

@[simp] theorem encode_length (message : StartOfOutrightInstrumentSnapshotMessage) : (encode message).length = 130 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, LogicalExpiry.encode_length]

theorem encode_length_pos (message : StartOfOutrightInstrumentSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfOutrightInstrumentSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [LogicalExpiry.decode_encode, some_bind]
  rfl

end StartOfOutrightInstrumentSnapshotMessage

/-- Start Of Spread Instrument Snapshot Message: 131 bytes -/
structure StartOfSpreadInstrumentSnapshotMessage where
  snapshotSeqNum : BitVec 16
  lastInstrSeqNum : BitVec 32
  symbol : Alpha 24
  productCode : Alpha 8
  description : Alpha 32
  tickSize : BitVec 64
  cfiCode : Alpha 8
  currency : Alpha 8
  productId : BitVec 32
  oldContractSize : BitVec 32
  orderCount : BitVec 32
  firstTradingSessionDate : BitVec 16
  lastTradingSessionDate : BitVec 16
  tradingSessionDate : BitVec 16
  productGroup : BitVec 8
  tradingStatus : BitVec 8
  leg1InstrumentId : BitVec 32
  leg2InstrumentId : BitVec 32
  spreadBuyConvention : BitVec 8
  logicalExpiry : LogicalExpiry
  deriving DecidableEq, Repr

namespace StartOfSpreadInstrumentSnapshotMessage

def encode (message : StartOfSpreadInstrumentSnapshotMessage) : List UInt8 :=
  encodeUIntLE 2 message.snapshotSeqNum
    ++ (encodeUIntLE 4 message.lastInstrSeqNum
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.description
    ++ (encodeUIntLE 8 message.tickSize
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.oldContractSize
    ++ (encodeUIntLE 4 message.orderCount
    ++ (encodeUIntLE 2 message.firstTradingSessionDate
    ++ (encodeUIntLE 2 message.lastTradingSessionDate
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (encodeUInt 1 message.productGroup
    ++ (encodeUInt 1 message.tradingStatus
    ++ (encodeUIntLE 4 message.leg1InstrumentId
    ++ (encodeUIntLE 4 message.leg2InstrumentId
    ++ (encodeUInt 1 message.spreadBuyConvention
    ++ (LogicalExpiry.encode message.logicalExpiry)))))))))))))))))))

def decode (bytes : List UInt8) : Option (StartOfSpreadInstrumentSnapshotMessage × List UInt8) := do
  let (snapshotSeqNum, bytes) ← decodeUIntLE 2 bytes
  let (lastInstrSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 24 bytes
  let (productCode, bytes) ← Alpha.decode 8 bytes
  let (description, bytes) ← Alpha.decode 32 bytes
  let (tickSize, bytes) ← decodeUIntLE 8 bytes
  let (cfiCode, bytes) ← Alpha.decode 8 bytes
  let (currency, bytes) ← Alpha.decode 8 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (oldContractSize, bytes) ← decodeUIntLE 4 bytes
  let (orderCount, bytes) ← decodeUIntLE 4 bytes
  let (firstTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (lastTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (productGroup, bytes) ← decodeUInt 1 bytes
  let (tradingStatus, bytes) ← decodeUInt 1 bytes
  let (leg1InstrumentId, bytes) ← decodeUIntLE 4 bytes
  let (leg2InstrumentId, bytes) ← decodeUIntLE 4 bytes
  let (spreadBuyConvention, bytes) ← decodeUInt 1 bytes
  let (logicalExpiry, bytes) ← LogicalExpiry.decode bytes
  pure ({ snapshotSeqNum, lastInstrSeqNum, symbol, productCode, description, tickSize, cfiCode, currency, productId, oldContractSize, orderCount, firstTradingSessionDate, lastTradingSessionDate, tradingSessionDate, productGroup, tradingStatus, leg1InstrumentId, leg2InstrumentId, spreadBuyConvention, logicalExpiry }, bytes)

@[simp] theorem encode_length (message : StartOfSpreadInstrumentSnapshotMessage) : (encode message).length = 131 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, LogicalExpiry.encode_length]

theorem encode_length_pos (message : StartOfSpreadInstrumentSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfSpreadInstrumentSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [LogicalExpiry.decode_encode, some_bind]
  rfl

end StartOfSpreadInstrumentSnapshotMessage

/-- Start Of Option Instrument Snapshot Message: 141 bytes -/
structure StartOfOptionInstrumentSnapshotMessage where
  snapshotSeqNum : BitVec 16
  lastInstrSeqNum : BitVec 32
  symbol : Alpha 24
  productCode : Alpha 8
  description : Alpha 32
  smallTick : BitVec 64
  cfiCode : Alpha 8
  largeTick : BitVec 64
  largeTickThreshold : BitVec 64
  strikePrice : BitVec 64
  productId : BitVec 32
  underlyingInstrumentId : BitVec 32
  orderCount : BitVec 32
  firstTradingSessionDate : BitVec 16
  lastTradingSessionDate : BitVec 16
  tradingSessionDate : BitVec 16
  productGroup : BitVec 8
  tradingStatus : BitVec 8
  definitionFlags : BitVec 16
  optionExpiryType : BitVec 8
  logicalExpiry : LogicalExpiry
  deriving DecidableEq, Repr

namespace StartOfOptionInstrumentSnapshotMessage

def encode (message : StartOfOptionInstrumentSnapshotMessage) : List UInt8 :=
  encodeUIntLE 2 message.snapshotSeqNum
    ++ (encodeUIntLE 4 message.lastInstrSeqNum
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.description
    ++ (encodeUIntLE 8 message.smallTick
    ++ (Alpha.encode message.cfiCode
    ++ (encodeUIntLE 8 message.largeTick
    ++ (encodeUIntLE 8 message.largeTickThreshold
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.underlyingInstrumentId
    ++ (encodeUIntLE 4 message.orderCount
    ++ (encodeUIntLE 2 message.firstTradingSessionDate
    ++ (encodeUIntLE 2 message.lastTradingSessionDate
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (encodeUInt 1 message.productGroup
    ++ (encodeUInt 1 message.tradingStatus
    ++ (encodeUIntLE 2 message.definitionFlags
    ++ (encodeUInt 1 message.optionExpiryType
    ++ (LogicalExpiry.encode message.logicalExpiry))))))))))))))))))))

def decode (bytes : List UInt8) : Option (StartOfOptionInstrumentSnapshotMessage × List UInt8) := do
  let (snapshotSeqNum, bytes) ← decodeUIntLE 2 bytes
  let (lastInstrSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 24 bytes
  let (productCode, bytes) ← Alpha.decode 8 bytes
  let (description, bytes) ← Alpha.decode 32 bytes
  let (smallTick, bytes) ← decodeUIntLE 8 bytes
  let (cfiCode, bytes) ← Alpha.decode 8 bytes
  let (largeTick, bytes) ← decodeUIntLE 8 bytes
  let (largeTickThreshold, bytes) ← decodeUIntLE 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingInstrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderCount, bytes) ← decodeUIntLE 4 bytes
  let (firstTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (lastTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (productGroup, bytes) ← decodeUInt 1 bytes
  let (tradingStatus, bytes) ← decodeUInt 1 bytes
  let (definitionFlags, bytes) ← decodeUIntLE 2 bytes
  let (optionExpiryType, bytes) ← decodeUInt 1 bytes
  let (logicalExpiry, bytes) ← LogicalExpiry.decode bytes
  pure ({ snapshotSeqNum, lastInstrSeqNum, symbol, productCode, description, smallTick, cfiCode, largeTick, largeTickThreshold, strikePrice, productId, underlyingInstrumentId, orderCount, firstTradingSessionDate, lastTradingSessionDate, tradingSessionDate, productGroup, tradingStatus, definitionFlags, optionExpiryType, logicalExpiry }, bytes)

@[simp] theorem encode_length (message : StartOfOptionInstrumentSnapshotMessage) : (encode message).length = 141 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, LogicalExpiry.encode_length]

theorem encode_length_pos (message : StartOfOptionInstrumentSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfOptionInstrumentSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [LogicalExpiry.decode_encode, some_bind]
  rfl

end StartOfOptionInstrumentSnapshotMessage

/-- Order Snapshot Message: 30 bytes -/
structure OrderSnapshotMessage where
  snapshotSeqNum : BitVec 16
  quantity : BitVec 32
  transactTime : BitVec 64
  orderId : BitVec 64
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderSnapshotMessage

def encode (message : OrderSnapshotMessage) : List UInt8 :=
  encodeUIntLE 2 message.snapshotSeqNum
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price))))

def decode (bytes : List UInt8) : Option (OrderSnapshotMessage × List UInt8) := do
  let (snapshotSeqNum, bytes) ← decodeUIntLE 2 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ snapshotSeqNum, quantity, transactTime, orderId, price }, bytes)

@[simp] theorem encode_length (message : OrderSnapshotMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderSnapshotMessage) (rest : List UInt8) :
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

end OrderSnapshotMessage

/-- End Of Snapshot Message: 160 bytes -/
structure EndOfSnapshotMessage where
  snapshotSeqNum : BitVec 16
  tradeVolume : BitVec 32
  indicativeOpenPrice : BitVec 64
  dayOpenPrice : BitVec 64
  closePrice : BitVec 64
  lowPrice : BitVec 64
  highPrice : BitVec 64
  vwapPriceOptional : BitVec 64
  settlementPrice : BitVec 64
  lastTradePrice : BitVec 64
  lastTradeTime : BitVec 64
  bestBidImpliedPrice : BitVec 64
  bestAskImpliedPrice : BitVec 64
  nextBidImpliedPrice : BitVec 64
  nextAskImpliedPrice : BitVec 64
  limitDownPrice : BitVec 64
  limitUpPrice : BitVec 64
  lastTradeQty : BitVec 32
  openInterest : BitVec 32
  bestBidImpliedQty : BitVec 32
  bestAskImpliedQty : BitVec 32
  nextBidImpliedQty : BitVec 32
  nextAskImpliedQty : BitVec 32
  priorSettlementPriceOptional : BitVec 64
  definitionFlags : BitVec 16
  deriving DecidableEq, Repr

namespace EndOfSnapshotMessage

def encode (message : EndOfSnapshotMessage) : List UInt8 :=
  encodeUIntLE 2 message.snapshotSeqNum
    ++ (encodeUIntLE 4 message.tradeVolume
    ++ (encodeUIntLE 8 message.indicativeOpenPrice
    ++ (encodeUIntLE 8 message.dayOpenPrice
    ++ (encodeUIntLE 8 message.closePrice
    ++ (encodeUIntLE 8 message.lowPrice
    ++ (encodeUIntLE 8 message.highPrice
    ++ (encodeUIntLE 8 message.vwapPriceOptional
    ++ (encodeUIntLE 8 message.settlementPrice
    ++ (encodeUIntLE 8 message.lastTradePrice
    ++ (encodeUIntLE 8 message.lastTradeTime
    ++ (encodeUIntLE 8 message.bestBidImpliedPrice
    ++ (encodeUIntLE 8 message.bestAskImpliedPrice
    ++ (encodeUIntLE 8 message.nextBidImpliedPrice
    ++ (encodeUIntLE 8 message.nextAskImpliedPrice
    ++ (encodeUIntLE 8 message.limitDownPrice
    ++ (encodeUIntLE 8 message.limitUpPrice
    ++ (encodeUIntLE 4 message.lastTradeQty
    ++ (encodeUIntLE 4 message.openInterest
    ++ (encodeUIntLE 4 message.bestBidImpliedQty
    ++ (encodeUIntLE 4 message.bestAskImpliedQty
    ++ (encodeUIntLE 4 message.nextBidImpliedQty
    ++ (encodeUIntLE 4 message.nextAskImpliedQty
    ++ (encodeUIntLE 8 message.priorSettlementPriceOptional
    ++ (encodeUIntLE 2 message.definitionFlags))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (EndOfSnapshotMessage × List UInt8) := do
  let (snapshotSeqNum, bytes) ← decodeUIntLE 2 bytes
  let (tradeVolume, bytes) ← decodeUIntLE 4 bytes
  let (indicativeOpenPrice, bytes) ← decodeUIntLE 8 bytes
  let (dayOpenPrice, bytes) ← decodeUIntLE 8 bytes
  let (closePrice, bytes) ← decodeUIntLE 8 bytes
  let (lowPrice, bytes) ← decodeUIntLE 8 bytes
  let (highPrice, bytes) ← decodeUIntLE 8 bytes
  let (vwapPriceOptional, bytes) ← decodeUIntLE 8 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (lastTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (lastTradeTime, bytes) ← decodeUIntLE 8 bytes
  let (bestBidImpliedPrice, bytes) ← decodeUIntLE 8 bytes
  let (bestAskImpliedPrice, bytes) ← decodeUIntLE 8 bytes
  let (nextBidImpliedPrice, bytes) ← decodeUIntLE 8 bytes
  let (nextAskImpliedPrice, bytes) ← decodeUIntLE 8 bytes
  let (limitDownPrice, bytes) ← decodeUIntLE 8 bytes
  let (limitUpPrice, bytes) ← decodeUIntLE 8 bytes
  let (lastTradeQty, bytes) ← decodeUIntLE 4 bytes
  let (openInterest, bytes) ← decodeUIntLE 4 bytes
  let (bestBidImpliedQty, bytes) ← decodeUIntLE 4 bytes
  let (bestAskImpliedQty, bytes) ← decodeUIntLE 4 bytes
  let (nextBidImpliedQty, bytes) ← decodeUIntLE 4 bytes
  let (nextAskImpliedQty, bytes) ← decodeUIntLE 4 bytes
  let (priorSettlementPriceOptional, bytes) ← decodeUIntLE 8 bytes
  let (definitionFlags, bytes) ← decodeUIntLE 2 bytes
  pure ({ snapshotSeqNum, tradeVolume, indicativeOpenPrice, dayOpenPrice, closePrice, lowPrice, highPrice, vwapPriceOptional, settlementPrice, lastTradePrice, lastTradeTime, bestBidImpliedPrice, bestAskImpliedPrice, nextBidImpliedPrice, nextAskImpliedPrice, limitDownPrice, limitUpPrice, lastTradeQty, openInterest, bestBidImpliedQty, bestAskImpliedQty, nextBidImpliedQty, nextAskImpliedQty, priorSettlementPriceOptional, definitionFlags }, bytes)

@[simp] theorem encode_length (message : EndOfSnapshotMessage) : (encode message).length = 160 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : EndOfSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : EndOfSnapshotMessage) (rest : List UInt8) :
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

end EndOfSnapshotMessage

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
  messageCount : BitVec 8
  deriving DecidableEq, Repr

namespace RetransmitRequestMessage

def encode (message : RetransmitRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.beginSeqNum
    ++ (encodeUInt 1 message.messageCount)

def decode (bytes : List UInt8) : Option (RetransmitRequestMessage × List UInt8) := do
  let (beginSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (messageCount, bytes) ← decodeUInt 1 bytes
  pure ({ beginSeqNum, messageCount }, bytes)

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
  | outrightInstrumentDefinitionMessage (message : OutrightInstrumentDefinitionMessage) -- 10
  | spreadInstrumentDefinitionMessage (message : SpreadInstrumentDefinitionMessage) -- 11
  | optionInstrumentDefinitionMessage (message : OptionInstrumentDefinitionMessage) -- 12
  | tradingStatusUpdateMessage (message : TradingStatusUpdateMessage) -- 17
  | orderPutMessage (message : OrderPutMessage) -- 20
  | orderDeleteMessage (message : OrderDeleteMessage) -- 21
  | impliedOrderUpdateMessage (message : ImpliedOrderUpdateMessage) -- 22
  | tradeSummaryMessage (message : TradeSummaryMessage) -- 33
  | tradeMessage (message : TradeMessage) -- 30
  | tradeAmendMessage (message : TradeAmendMessage) -- 31
  | spreadTradeAmendMessage (message : SpreadTradeAmendMessage) -- 34
  | tradeBustMessage (message : TradeBustMessage) -- 32
  | marketStatMessage (message : MarketStatMessage) -- 40
  | tradeSessionVolumeMessage (message : TradeSessionVolumeMessage) -- 41
  | openInterestMessage (message : OpenInterestMessage) -- 42
  | startOfOutrightInstrumentSnapshotMessage (message : StartOfOutrightInstrumentSnapshotMessage) -- 110
  | startOfSpreadInstrumentSnapshotMessage (message : StartOfSpreadInstrumentSnapshotMessage) -- 111
  | startOfOptionInstrumentSnapshotMessage (message : StartOfOptionInstrumentSnapshotMessage) -- 112
  | orderSnapshotMessage (message : OrderSnapshotMessage) -- 120
  | endOfSnapshotMessage (message : EndOfSnapshotMessage) -- 122
  | endOfCycleMessage (message : EndOfCycleMessage) -- 124
  | retransmitRequestMessage (message : RetransmitRequestMessage) -- 200
  | retransmitRejectMessage (message : RetransmitRejectMessage) -- 202
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .outrightInstrumentDefinitionMessage _ => 10
  | .spreadInstrumentDefinitionMessage _ => 11
  | .optionInstrumentDefinitionMessage _ => 12
  | .tradingStatusUpdateMessage _ => 17
  | .orderPutMessage _ => 20
  | .orderDeleteMessage _ => 21
  | .impliedOrderUpdateMessage _ => 22
  | .tradeSummaryMessage _ => 33
  | .tradeMessage _ => 30
  | .tradeAmendMessage _ => 31
  | .spreadTradeAmendMessage _ => 34
  | .tradeBustMessage _ => 32
  | .marketStatMessage _ => 40
  | .tradeSessionVolumeMessage _ => 41
  | .openInterestMessage _ => 42
  | .startOfOutrightInstrumentSnapshotMessage _ => 110
  | .startOfSpreadInstrumentSnapshotMessage _ => 111
  | .startOfOptionInstrumentSnapshotMessage _ => 112
  | .orderSnapshotMessage _ => 120
  | .endOfSnapshotMessage _ => 122
  | .endOfCycleMessage _ => 124
  | .retransmitRequestMessage _ => 200
  | .retransmitRejectMessage _ => 202

def encode : Payload → List UInt8
  | .outrightInstrumentDefinitionMessage message => OutrightInstrumentDefinitionMessage.encode message
  | .spreadInstrumentDefinitionMessage message => SpreadInstrumentDefinitionMessage.encode message
  | .optionInstrumentDefinitionMessage message => OptionInstrumentDefinitionMessage.encode message
  | .tradingStatusUpdateMessage message => TradingStatusUpdateMessage.encode message
  | .orderPutMessage message => OrderPutMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .impliedOrderUpdateMessage message => ImpliedOrderUpdateMessage.encode message
  | .tradeSummaryMessage message => TradeSummaryMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .tradeAmendMessage message => TradeAmendMessage.encode message
  | .spreadTradeAmendMessage message => SpreadTradeAmendMessage.encode message
  | .tradeBustMessage message => TradeBustMessage.encode message
  | .marketStatMessage message => MarketStatMessage.encode message
  | .tradeSessionVolumeMessage message => TradeSessionVolumeMessage.encode message
  | .openInterestMessage message => OpenInterestMessage.encode message
  | .startOfOutrightInstrumentSnapshotMessage message => StartOfOutrightInstrumentSnapshotMessage.encode message
  | .startOfSpreadInstrumentSnapshotMessage message => StartOfSpreadInstrumentSnapshotMessage.encode message
  | .startOfOptionInstrumentSnapshotMessage message => StartOfOptionInstrumentSnapshotMessage.encode message
  | .orderSnapshotMessage message => OrderSnapshotMessage.encode message
  | .endOfSnapshotMessage message => EndOfSnapshotMessage.encode message
  | .endOfCycleMessage message => EndOfCycleMessage.encode message
  | .retransmitRequestMessage message => RetransmitRequestMessage.encode message
  | .retransmitRejectMessage message => RetransmitRejectMessage.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 10 then (OutrightInstrumentDefinitionMessage.decode bytes).map fun (message, rest) => (.outrightInstrumentDefinitionMessage message, rest)
  else if tag = 11 then (SpreadInstrumentDefinitionMessage.decode bytes).map fun (message, rest) => (.spreadInstrumentDefinitionMessage message, rest)
  else if tag = 12 then (OptionInstrumentDefinitionMessage.decode bytes).map fun (message, rest) => (.optionInstrumentDefinitionMessage message, rest)
  else if tag = 17 then (TradingStatusUpdateMessage.decode bytes).map fun (message, rest) => (.tradingStatusUpdateMessage message, rest)
  else if tag = 20 then (OrderPutMessage.decode bytes).map fun (message, rest) => (.orderPutMessage message, rest)
  else if tag = 21 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 22 then (ImpliedOrderUpdateMessage.decode bytes).map fun (message, rest) => (.impliedOrderUpdateMessage message, rest)
  else if tag = 33 then (TradeSummaryMessage.decode bytes).map fun (message, rest) => (.tradeSummaryMessage message, rest)
  else if tag = 30 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 31 then (TradeAmendMessage.decode bytes).map fun (message, rest) => (.tradeAmendMessage message, rest)
  else if tag = 34 then (SpreadTradeAmendMessage.decode bytes).map fun (message, rest) => (.spreadTradeAmendMessage message, rest)
  else if tag = 32 then (TradeBustMessage.decode bytes).map fun (message, rest) => (.tradeBustMessage message, rest)
  else if tag = 40 then (MarketStatMessage.decode bytes).map fun (message, rest) => (.marketStatMessage message, rest)
  else if tag = 41 then (TradeSessionVolumeMessage.decode bytes).map fun (message, rest) => (.tradeSessionVolumeMessage message, rest)
  else if tag = 42 then (OpenInterestMessage.decode bytes).map fun (message, rest) => (.openInterestMessage message, rest)
  else if tag = 110 then (StartOfOutrightInstrumentSnapshotMessage.decode bytes).map fun (message, rest) => (.startOfOutrightInstrumentSnapshotMessage message, rest)
  else if tag = 111 then (StartOfSpreadInstrumentSnapshotMessage.decode bytes).map fun (message, rest) => (.startOfSpreadInstrumentSnapshotMessage message, rest)
  else if tag = 112 then (StartOfOptionInstrumentSnapshotMessage.decode bytes).map fun (message, rest) => (.startOfOptionInstrumentSnapshotMessage message, rest)
  else if tag = 120 then (OrderSnapshotMessage.decode bytes).map fun (message, rest) => (.orderSnapshotMessage message, rest)
  else if tag = 122 then (EndOfSnapshotMessage.decode bytes).map fun (message, rest) => (.endOfSnapshotMessage message, rest)
  else if tag = 124 then (EndOfCycleMessage.decode bytes).map fun (message, rest) => (.endOfCycleMessage message, rest)
  else if tag = 200 then (RetransmitRequestMessage.decode bytes).map fun (message, rest) => (.retransmitRequestMessage message, rest)
  else if tag = 202 then (RetransmitRejectMessage.decode bytes).map fun (message, rest) => (.retransmitRejectMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Sbe Message -/
structure SbeMessage where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  padding : Capped 65350
  deriving DecidableEq, Repr

namespace SbeMessage

def encodeBody (message : SbeMessage) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload
    ++ (message.padding.val)))))

def decodeBody (bytes : List UInt8) : Option SbeMessage := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  let padding_ := bytes
  if fits_padding : padding_.length ≤ 65350 then
    pure { blockLength, schemaId, version, payload, padding := ⟨padding_, fits_padding⟩ }
  else none

theorem decodeBody_encodeBody (message : SbeMessage) : decodeBody (encodeBody message) = some message := by
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
theorem encodeBody_length_lt (message : SbeMessage) : (encodeBody message).length + 2 < 256 ^ 2 := by
  have bound_padding := message.padding.length_le
  unfold encodeBody
  cases message.payload with
  | outrightInstrumentDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OutrightInstrumentDefinitionMessage.encode_length]
    omega
  | spreadInstrumentDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SpreadInstrumentDefinitionMessage.encode_length]
    omega
  | optionInstrumentDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OptionInstrumentDefinitionMessage.encode_length]
    omega
  | tradingStatusUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradingStatusUpdateMessage.encode_length]
    omega
  | orderPutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderPutMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderDeleteMessage.encode_length]
    omega
  | impliedOrderUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ImpliedOrderUpdateMessage.encode_length]
    omega
  | tradeSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeSummaryMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeMessage.encode_length]
    omega
  | tradeAmendMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeAmendMessage.encode_length]
    omega
  | spreadTradeAmendMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SpreadTradeAmendMessage.encode_length]
    omega
  | tradeBustMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeBustMessage.encode_length]
    omega
  | marketStatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MarketStatMessage.encode_length]
    omega
  | tradeSessionVolumeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeSessionVolumeMessage.encode_length]
    omega
  | openInterestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OpenInterestMessage.encode_length]
    omega
  | startOfOutrightInstrumentSnapshotMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, StartOfOutrightInstrumentSnapshotMessage.encode_length]
    omega
  | startOfSpreadInstrumentSnapshotMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, StartOfSpreadInstrumentSnapshotMessage.encode_length]
    omega
  | startOfOptionInstrumentSnapshotMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, StartOfOptionInstrumentSnapshotMessage.encode_length]
    omega
  | orderSnapshotMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderSnapshotMessage.encode_length]
    omega
  | endOfSnapshotMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EndOfSnapshotMessage.encode_length]
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

/-- Size rule: Frame Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : SbeMessage → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (SbeMessage × List UInt8) :=
  decodeFramedAllLE 2 2 decodeBody

@[simp] theorem decode_encode (message : SbeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : SbeMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end SbeMessage

/-- Packet -/
structure Packet where
  packetHeader : PacketHeader
  sbeMessage : List SbeMessage
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  PacketHeader.encode message.packetHeader
    ++ (encodeMany SbeMessage.encode message.sbeMessage)

def decode (bytes : List UInt8) : Option Packet := do
  let (packetHeader, bytes) ← PacketHeader.decode bytes
  let sbeMessage ← decodeAll SbeMessage.decode bytes.length bytes
  pure { packetHeader, sbeMessage }

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [PacketHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [PacketHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeAll_encodeMany SbeMessage.encode SbeMessage.decode SbeMessage.decode_encode SbeMessage.encode_length_pos message.sbeMessage _ (encodeMany_length_ge SbeMessage.encode SbeMessage.encode_length_pos message.sbeMessage), some_bind]
  rfl

end Packet

end Omi.CoinbaseCoinbasederivativesMarketdataapiSbeV17
