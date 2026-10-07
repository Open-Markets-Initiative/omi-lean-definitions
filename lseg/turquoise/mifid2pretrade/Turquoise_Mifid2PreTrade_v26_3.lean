import Wire

/-!
# London Stock Exchange MiFID II Pre Trade v26.3

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Allowed Book Types is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Order Book Update is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LsegTurquoiseMifid2pretradeGtpV263

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x43, 0x4F]

inductive EventCode where
  | endOfDay -- End Of Day
  | startOfDay -- Start Of Day
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .endOfDay => 0x43
  | .startOfDay => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x43 then .endOfDay
  else .startOfDay

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | endOfDay => decide
  | startOfDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x48, 0x4A, 0x4B, 0x50, 0x54, 0x74, 0x63, 0x32, 0x77]

inductive TradingStatus where
  | halted -- Halted
  | haltedMatchingPartitionSuspended -- Halted Matching Partition Suspended
  | haltedSystemSuspended -- Halted System Suspended
  | haltedRegulatoryHalt -- Halted Regulatory Halt
  | regularTradingStartOfTrqbSession -- Regular Trading Start Of Trqb Session
  | endOfRegularTradingEndOfTrqbSession -- End Of Regular Trading End Of Trqb Session
  | closed -- Closed
  | suspended -- Suspended
  | noActiveSession -- No Active Session
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .halted => 0x48
  | .haltedMatchingPartitionSuspended => 0x4A
  | .haltedSystemSuspended => 0x4B
  | .haltedRegulatoryHalt => 0x50
  | .regularTradingStartOfTrqbSession => 0x54
  | .endOfRegularTradingEndOfTrqbSession => 0x74
  | .closed => 0x63
  | .suspended => 0x32
  | .noActiveSession => 0x77
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x48 then .halted
  else if byte = 0x4A then .haltedMatchingPartitionSuspended
  else if byte = 0x4B then .haltedSystemSuspended
  else if byte = 0x50 then .haltedRegulatoryHalt
  else if byte = 0x54 then .regularTradingStartOfTrqbSession
  else if byte = 0x74 then .endOfRegularTradingEndOfTrqbSession
  else if byte = 0x63 then .closed
  else if byte = 0x32 then .suspended
  else .noActiveSession

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | haltedMatchingPartitionSuspended => decide
  | haltedSystemSuspended => decide
  | haltedRegulatoryHalt => decide
  | regularTradingStartOfTrqbSession => decide
  | endOfRegularTradingEndOfTrqbSession => decide
  | closed => decide
  | suspended => decide
  | noActiveSession => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingStatus

/-- System Event Message: 11 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 64
  eventCode : EventCode
  sourceVenue : BitVec 16
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (EventCode.encode message.eventCode
    ++ (encodeUIntLE 2 message.sourceVenue))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  pure ({ timestamp, eventCode, sourceVenue }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SystemEventMessage

/-- Instrument Directory Message: 138 bytes -/
structure InstrumentDirectoryMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  isin : Alpha 12
  allowedBookTypes : BitVec 8
  sourceVenue : BitVec 16
  venueInstrumentId : Alpha 11
  tickId : Alpha 2
  reserved8 : Alpha 8
  dynamicCircuitBreakerTolerances : BitVec 64
  staticCircuitBreakerTolerances : BitVec 64
  segment : Alpha 6
  reserved12 : Alpha 12
  securityExchange : Alpha 11
  currency : Alpha 3
  partitionId : Alpha 1
  reserved4 : Alpha 4
  averageDailyTurnoverAdt : BitVec 64
  secondReserved8 : Alpha 8
  reserved1 : Alpha 1
  thirdReserved8 : Alpha 8
  fourthReserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace InstrumentDirectoryMessage

def encode (message : InstrumentDirectoryMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (Alpha.encode message.isin
    ++ (encodeUIntLE 1 message.allowedBookTypes
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (Alpha.encode message.venueInstrumentId
    ++ (Alpha.encode message.tickId
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 8 message.dynamicCircuitBreakerTolerances
    ++ (encodeUIntLE 8 message.staticCircuitBreakerTolerances
    ++ (Alpha.encode message.segment
    ++ (Alpha.encode message.reserved12
    ++ (Alpha.encode message.securityExchange
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.partitionId
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 8 message.averageDailyTurnoverAdt
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.thirdReserved8
    ++ (Alpha.encode message.fourthReserved8))))))))))))))))))))

def decode (bytes : List UInt8) : Option (InstrumentDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (allowedBookTypes, bytes) ← decodeUIntLE 1 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (venueInstrumentId, bytes) ← Alpha.decode 11 bytes
  let (tickId, bytes) ← Alpha.decode 2 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (dynamicCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (staticCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (segment, bytes) ← Alpha.decode 6 bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  let (securityExchange, bytes) ← Alpha.decode 11 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (partitionId, bytes) ← Alpha.decode 1 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (averageDailyTurnoverAdt, bytes) ← decodeUIntLE 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved8, bytes) ← Alpha.decode 8 bytes
  let (fourthReserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ timestamp, instrument, isin, allowedBookTypes, sourceVenue, venueInstrumentId, tickId, reserved8, dynamicCircuitBreakerTolerances, staticCircuitBreakerTolerances, segment, reserved12, securityExchange, currency, partitionId, reserved4, averageDailyTurnoverAdt, secondReserved8, reserved1, thirdReserved8, fourthReserved8 }, bytes)

@[simp] theorem encode_length (message : InstrumentDirectoryMessage) : (encode message).length = 138 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentDirectoryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentDirectoryMessage

/-- Instrument Directory Extended Message: 310 bytes -/
structure InstrumentDirectoryExtendedMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  isin : Alpha 12
  sedol : Alpha 8
  allowedBookTypes : BitVec 8
  sourceVenue : BitVec 16
  venueInstrumentId : Alpha 11
  segment : Alpha 6
  currency : Alpha 3
  tickId : Alpha 2
  previousDaysClosingPrice : BitVec 64
  reserved8 : Alpha 8
  dynamicCircuitBreakerTolerances : BitVec 64
  staticCircuitBreakerTolerances : BitVec 64
  firstReserved1 : Alpha 1
  secondReserved1 : Alpha 1
  expirationDate : Alpha 8
  listingStartDate : Alpha 8
  listingEndDate : Alpha 8
  minimumLotMinimumExecutionSize : BitVec 64
  lastPriceInPrecedingSession : BitVec 64
  lastPriceInPrecedingSessionDate : Alpha 8
  thirdReserved1 : Alpha 1
  secondReserved8 : Alpha 8
  thirdReserved8 : Alpha 8
  exMarkerCode : Alpha 2
  securityType : BitVec 8
  countryOfRegister : Alpha 3
  exchangeMarketSize : BitVec 64
  minimumPeakSizeMultiplier : BitVec 64
  securityMaximumSpread : BitVec 64
  clearingType : BitVec 8
  strikePrice : BitVec 64
  securityExchange : Alpha 11
  reserved12 : Alpha 12
  fourthReserved1 : Alpha 1
  fourthReserved8 : Alpha 8
  fifthReserved8 : Alpha 8
  partitionId : Alpha 1
  sixthReserved8 : Alpha 8
  seventhReserved8 : Alpha 8
  reserved4 : Alpha 4
  reserved2 : Alpha 2
  symbol : Alpha 8
  description : Alpha 40
  deriving DecidableEq, Repr

namespace InstrumentDirectoryExtendedMessage

def encode (message : InstrumentDirectoryExtendedMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.sedol
    ++ (encodeUIntLE 1 message.allowedBookTypes
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (Alpha.encode message.venueInstrumentId
    ++ (Alpha.encode message.segment
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.tickId
    ++ (encodeUIntLE 8 message.previousDaysClosingPrice
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 8 message.dynamicCircuitBreakerTolerances
    ++ (encodeUIntLE 8 message.staticCircuitBreakerTolerances
    ++ (Alpha.encode message.firstReserved1
    ++ (Alpha.encode message.secondReserved1
    ++ (Alpha.encode message.expirationDate
    ++ (Alpha.encode message.listingStartDate
    ++ (Alpha.encode message.listingEndDate
    ++ (encodeUIntLE 8 message.minimumLotMinimumExecutionSize
    ++ (encodeUIntLE 8 message.lastPriceInPrecedingSession
    ++ (Alpha.encode message.lastPriceInPrecedingSessionDate
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.thirdReserved8
    ++ (Alpha.encode message.exMarkerCode
    ++ (encodeUIntLE 1 message.securityType
    ++ (Alpha.encode message.countryOfRegister
    ++ (encodeUIntLE 8 message.exchangeMarketSize
    ++ (encodeUIntLE 8 message.minimumPeakSizeMultiplier
    ++ (encodeUIntLE 8 message.securityMaximumSpread
    ++ (encodeUIntLE 1 message.clearingType
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (Alpha.encode message.securityExchange
    ++ (Alpha.encode message.reserved12
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.fourthReserved8
    ++ (Alpha.encode message.fifthReserved8
    ++ (Alpha.encode message.partitionId
    ++ (Alpha.encode message.sixthReserved8
    ++ (Alpha.encode message.seventhReserved8
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.description))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (InstrumentDirectoryExtendedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (sedol, bytes) ← Alpha.decode 8 bytes
  let (allowedBookTypes, bytes) ← decodeUIntLE 1 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (venueInstrumentId, bytes) ← Alpha.decode 11 bytes
  let (segment, bytes) ← Alpha.decode 6 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (tickId, bytes) ← Alpha.decode 2 bytes
  let (previousDaysClosingPrice, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (dynamicCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (staticCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (firstReserved1, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (expirationDate, bytes) ← Alpha.decode 8 bytes
  let (listingStartDate, bytes) ← Alpha.decode 8 bytes
  let (listingEndDate, bytes) ← Alpha.decode 8 bytes
  let (minimumLotMinimumExecutionSize, bytes) ← decodeUIntLE 8 bytes
  let (lastPriceInPrecedingSession, bytes) ← decodeUIntLE 8 bytes
  let (lastPriceInPrecedingSessionDate, bytes) ← Alpha.decode 8 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (thirdReserved8, bytes) ← Alpha.decode 8 bytes
  let (exMarkerCode, bytes) ← Alpha.decode 2 bytes
  let (securityType, bytes) ← decodeUIntLE 1 bytes
  let (countryOfRegister, bytes) ← Alpha.decode 3 bytes
  let (exchangeMarketSize, bytes) ← decodeUIntLE 8 bytes
  let (minimumPeakSizeMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (securityMaximumSpread, bytes) ← decodeUIntLE 8 bytes
  let (clearingType, bytes) ← decodeUIntLE 1 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (securityExchange, bytes) ← Alpha.decode 11 bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved8, bytes) ← Alpha.decode 8 bytes
  let (fifthReserved8, bytes) ← Alpha.decode 8 bytes
  let (partitionId, bytes) ← Alpha.decode 1 bytes
  let (sixthReserved8, bytes) ← Alpha.decode 8 bytes
  let (seventhReserved8, bytes) ← Alpha.decode 8 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (description, bytes) ← Alpha.decode 40 bytes
  pure ({ timestamp, instrument, isin, sedol, allowedBookTypes, sourceVenue, venueInstrumentId, segment, currency, tickId, previousDaysClosingPrice, reserved8, dynamicCircuitBreakerTolerances, staticCircuitBreakerTolerances, firstReserved1, secondReserved1, expirationDate, listingStartDate, listingEndDate, minimumLotMinimumExecutionSize, lastPriceInPrecedingSession, lastPriceInPrecedingSessionDate, thirdReserved1, secondReserved8, thirdReserved8, exMarkerCode, securityType, countryOfRegister, exchangeMarketSize, minimumPeakSizeMultiplier, securityMaximumSpread, clearingType, strikePrice, securityExchange, reserved12, fourthReserved1, fourthReserved8, fifthReserved8, partitionId, sixthReserved8, seventhReserved8, reserved4, reserved2, symbol, description }, bytes)

@[simp] theorem encode_length (message : InstrumentDirectoryExtendedMessage) : (encode message).length = 310 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentDirectoryExtendedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : InstrumentDirectoryExtendedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentDirectoryExtendedMessage

/-- Instrument Status Message: 27 bytes -/
structure InstrumentStatusMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  sourceVenue : BitVec 16
  tradingStatus : TradingStatus
  sessionChangeReason : BitVec 8
  newEndTime : Alpha 6
  orderBookType : BitVec 8
  deriving DecidableEq, Repr

namespace InstrumentStatusMessage

def encode (message : InstrumentStatusMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (TradingStatus.encode message.tradingStatus
    ++ (encodeUIntLE 1 message.sessionChangeReason
    ++ (Alpha.encode message.newEndTime
    ++ (encodeUIntLE 1 message.orderBookType))))))

def decode (bytes : List UInt8) : Option (InstrumentStatusMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (sessionChangeReason, bytes) ← decodeUIntLE 1 bytes
  let (newEndTime, bytes) ← Alpha.decode 6 bytes
  let (orderBookType, bytes) ← decodeUIntLE 1 bytes
  pure ({ timestamp, instrument, sourceVenue, tradingStatus, sessionChangeReason, newEndTime, orderBookType }, bytes)

@[simp] theorem encode_length (message : InstrumentStatusMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradingStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InstrumentStatusMessage

/-- Order Book Clear Message: 19 bytes -/
structure OrderBookClearMessage where
  timestamp : BitVec 64
  sourceVenue : BitVec 16
  instrument : BitVec 64
  orderBookType : BitVec 8
  deriving DecidableEq, Repr

namespace OrderBookClearMessage

def encode (message : OrderBookClearMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 1 message.orderBookType)))

def decode (bytes : List UInt8) : Option (OrderBookClearMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (orderBookType, bytes) ← decodeUIntLE 1 bytes
  pure ({ timestamp, sourceVenue, instrument, orderBookType }, bytes)

@[simp] theorem encode_length (message : OrderBookClearMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderBookClearMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookClearMessage) (rest : List UInt8) :
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

end OrderBookClearMessage

/-- Mifid Ii Order Book Update Message: 175 bytes -/
structure MifidIiOrderBookUpdateMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  sourceVenue : BitVec 16
  levelIdentifier : BitVec 8
  updateDateAndTime : Alpha 30
  instrumentIdentificationCode : Alpha 12
  orderBookSide : Alpha 4
  price : Alpha 20
  priceCurrency : Alpha 3
  priceNotation : Alpha 4
  quantity : Alpha 20
  aggregatedNoOfOrdersAndQuotes : Alpha 20
  venue : Alpha 4
  tradingSystem : Alpha 4
  tradingSystemPhase : Alpha 4
  publicationDateAndTime : Alpha 30
  orderBookUpdate : BitVec 8
  deriving DecidableEq, Repr

namespace MifidIiOrderBookUpdateMessage

def encode (message : MifidIiOrderBookUpdateMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 1 message.levelIdentifier
    ++ (Alpha.encode message.updateDateAndTime
    ++ (Alpha.encode message.instrumentIdentificationCode
    ++ (Alpha.encode message.orderBookSide
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.priceCurrency
    ++ (Alpha.encode message.priceNotation
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.aggregatedNoOfOrdersAndQuotes
    ++ (Alpha.encode message.venue
    ++ (Alpha.encode message.tradingSystem
    ++ (Alpha.encode message.tradingSystemPhase
    ++ (Alpha.encode message.publicationDateAndTime
    ++ (encodeUIntLE 1 message.orderBookUpdate))))))))))))))))

def decode (bytes : List UInt8) : Option (MifidIiOrderBookUpdateMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (levelIdentifier, bytes) ← decodeUIntLE 1 bytes
  let (updateDateAndTime, bytes) ← Alpha.decode 30 bytes
  let (instrumentIdentificationCode, bytes) ← Alpha.decode 12 bytes
  let (orderBookSide, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← Alpha.decode 20 bytes
  let (priceCurrency, bytes) ← Alpha.decode 3 bytes
  let (priceNotation, bytes) ← Alpha.decode 4 bytes
  let (quantity, bytes) ← Alpha.decode 20 bytes
  let (aggregatedNoOfOrdersAndQuotes, bytes) ← Alpha.decode 20 bytes
  let (venue, bytes) ← Alpha.decode 4 bytes
  let (tradingSystem, bytes) ← Alpha.decode 4 bytes
  let (tradingSystemPhase, bytes) ← Alpha.decode 4 bytes
  let (publicationDateAndTime, bytes) ← Alpha.decode 30 bytes
  let (orderBookUpdate, bytes) ← decodeUIntLE 1 bytes
  pure ({ timestamp, instrument, sourceVenue, levelIdentifier, updateDateAndTime, instrumentIdentificationCode, orderBookSide, price, priceCurrency, priceNotation, quantity, aggregatedNoOfOrdersAndQuotes, venue, tradingSystem, tradingSystemPhase, publicationDateAndTime, orderBookUpdate }, bytes)

@[simp] theorem encode_length (message : MifidIiOrderBookUpdateMessage) : (encode message).length = 175 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MifidIiOrderBookUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MifidIiOrderBookUpdateMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MifidIiOrderBookUpdateMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- 83
  | instrumentDirectoryMessage (message : InstrumentDirectoryMessage) -- 112
  | instrumentDirectoryExtendedMessage (message : InstrumentDirectoryExtendedMessage) -- 82
  | instrumentStatusMessage (message : InstrumentStatusMessage) -- 72
  | orderBookClearMessage (message : OrderBookClearMessage) -- 121
  | mifidIiOrderBookUpdateMessage (message : MifidIiOrderBookUpdateMessage) -- 98
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .instrumentDirectoryMessage _ => 112
  | .instrumentDirectoryExtendedMessage _ => 82
  | .instrumentStatusMessage _ => 72
  | .orderBookClearMessage _ => 121
  | .mifidIiOrderBookUpdateMessage _ => 98

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .instrumentDirectoryMessage message => InstrumentDirectoryMessage.encode message
  | .instrumentDirectoryExtendedMessage message => InstrumentDirectoryExtendedMessage.encode message
  | .instrumentStatusMessage message => InstrumentStatusMessage.encode message
  | .orderBookClearMessage message => OrderBookClearMessage.encode message
  | .mifidIiOrderBookUpdateMessage message => MifidIiOrderBookUpdateMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 310 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | instrumentDirectoryMessage inner =>
    simp only [encode, InstrumentDirectoryMessage.encode_length]
    omega
  | instrumentDirectoryExtendedMessage inner =>
    simp only [encode, InstrumentDirectoryExtendedMessage.encode_length]
    omega
  | instrumentStatusMessage inner =>
    simp only [encode, InstrumentStatusMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [encode, OrderBookClearMessage.encode_length]
    omega
  | mifidIiOrderBookUpdateMessage inner =>
    simp only [encode, MifidIiOrderBookUpdateMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 112 then (InstrumentDirectoryMessage.decode bytes).map fun (message, rest) => (.instrumentDirectoryMessage message, rest)
  else if tag = 82 then (InstrumentDirectoryExtendedMessage.decode bytes).map fun (message, rest) => (.instrumentDirectoryExtendedMessage message, rest)
  else if tag = 72 then (InstrumentStatusMessage.decode bytes).map fun (message, rest) => (.instrumentStatusMessage message, rest)
  else if tag = 121 then (OrderBookClearMessage.decode bytes).map fun (message, rest) => (.orderBookClearMessage message, rest)
  else if tag = 98 then (MifidIiOrderBookUpdateMessage.decode bytes).map fun (message, rest) => (.mifidIiOrderBookUpdateMessage message, rest)
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
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | instrumentDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InstrumentDirectoryMessage.encode_length]
    omega
  | instrumentDirectoryExtendedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InstrumentDirectoryExtendedMessage.encode_length]
    omega
  | instrumentStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InstrumentStatusMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookClearMessage.encode_length]
    omega
  | mifidIiOrderBookUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MifidIiOrderBookUpdateMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
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
  length : BitVec 16
  marketDataGroup : Alpha 1
  sequenceNumber : BitVec 32
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.length
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (Alpha.encode message.marketDataGroup
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeMany Message.encode message.message.val))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (length, bytes) ← decodeUIntLE 2 bytes
  let (messageCount, bytes) ← decodeUIntLE 1 bytes
  let (marketDataGroup, bytes) ← Alpha.decode 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ length, marketDataGroup, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.LsegTurquoiseMifid2pretradeGtpV263
