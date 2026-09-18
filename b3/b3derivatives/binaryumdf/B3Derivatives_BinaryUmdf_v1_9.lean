import Omi.Wire

/-!
# Brasil, Bolsa, Balcão Binary Unified Market Data Feed v1.9

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Match Event Indicator is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Imbalance Condition is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Trade Condition is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Match Event Indicator Optional is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Message's Message Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.B3B3derivativesBinaryumdfSbeV19

/-- Security Id Source: one byte code -/
def SecurityIdSource.codes : List UInt8 :=
  [0x34, 0x38]

inductive SecurityIdSource where
  | isin -- Isin
  | exchangeSymbol -- Exchange Symbol
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityIdSource.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityIdSource

def toByte : SecurityIdSource → UInt8
  | .isin => 0x34
  | .exchangeSymbol => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityIdSource :=
  if byte = 0x34 then .isin
  else .exchangeSymbol

def ofByte (byte : UInt8) : SecurityIdSource :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityIdSource) : ofByte value.toByte = value := by
  cases value with
  | isin => decide
  | exchangeSymbol => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityIdSource) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityIdSource × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityIdSource) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityIdSource) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityIdSource

/-- Security Update Action: one byte code -/
def SecurityUpdateAction.codes : List UInt8 :=
  [0x41, 0x44, 0x4D]

inductive SecurityUpdateAction where
  | add -- Add
  | delete -- Delete
  | modify -- Modify
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityUpdateAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityUpdateAction

def toByte : SecurityUpdateAction → UInt8
  | .add => 0x41
  | .delete => 0x44
  | .modify => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityUpdateAction :=
  if byte = 0x41 then .add
  else if byte = 0x44 then .delete
  else .modify

def ofByte (byte : UInt8) : SecurityUpdateAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityUpdateAction) : ofByte value.toByte = value := by
  cases value with
  | add => decide
  | delete => decide
  | modify => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityUpdateAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityUpdateAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityUpdateAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityUpdateAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityUpdateAction

/-- Md Entry Type: one byte code -/
def MdEntryType.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x42, 0x43, 0x4A, 0x63, 0x67, 0x68, 0x44, 0x73, 0x76, 0x75]

inductive MdEntryType where
  | bid -- Bid
  | offer -- Offer
  | trade -- Trade
  | indexValue -- Index Value
  | openingPrice -- Opening Price
  | closingPrice -- Closing Price
  | settlementPrice -- Settlement Price
  | sessionHighPrice -- Session High Price
  | sessionLowPrice -- Session Low Price
  | executionStatistics -- Execution Statistics
  | imbalance -- Imbalance
  | tradeVolume -- Trade Volume
  | openInterest -- Open Interest
  | emptyBook -- Empty Book
  | securityTradingStatePhase -- Security Trading State Phase
  | priceBand -- Price Band
  | quantityBand -- Quantity Band
  | compositeUnderlyingPrice -- Composite Underlying Price
  | executionSummary -- Execution Summary
  | volatilityPrice -- Volatility Price
  | tradeBust -- Trade Bust
  | unlisted (byte : { byte : UInt8 // byte ∉ MdEntryType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MdEntryType

def toByte : MdEntryType → UInt8
  | .bid => 0x30
  | .offer => 0x31
  | .trade => 0x32
  | .indexValue => 0x33
  | .openingPrice => 0x34
  | .closingPrice => 0x35
  | .settlementPrice => 0x36
  | .sessionHighPrice => 0x37
  | .sessionLowPrice => 0x38
  | .executionStatistics => 0x39
  | .imbalance => 0x41
  | .tradeVolume => 0x42
  | .openInterest => 0x43
  | .emptyBook => 0x4A
  | .securityTradingStatePhase => 0x63
  | .priceBand => 0x67
  | .quantityBand => 0x68
  | .compositeUnderlyingPrice => 0x44
  | .executionSummary => 0x73
  | .volatilityPrice => 0x76
  | .tradeBust => 0x75
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MdEntryType :=
  if byte = 0x30 then .bid
  else if byte = 0x31 then .offer
  else if byte = 0x32 then .trade
  else if byte = 0x33 then .indexValue
  else if byte = 0x34 then .openingPrice
  else if byte = 0x35 then .closingPrice
  else if byte = 0x36 then .settlementPrice
  else if byte = 0x37 then .sessionHighPrice
  else if byte = 0x38 then .sessionLowPrice
  else if byte = 0x39 then .executionStatistics
  else if byte = 0x41 then .imbalance
  else if byte = 0x42 then .tradeVolume
  else if byte = 0x43 then .openInterest
  else if byte = 0x4A then .emptyBook
  else if byte = 0x63 then .securityTradingStatePhase
  else if byte = 0x67 then .priceBand
  else if byte = 0x68 then .quantityBand
  else if byte = 0x44 then .compositeUnderlyingPrice
  else if byte = 0x73 then .executionSummary
  else if byte = 0x76 then .volatilityPrice
  else .tradeBust

def ofByte (byte : UInt8) : MdEntryType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MdEntryType) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | offer => decide
  | trade => decide
  | indexValue => decide
  | openingPrice => decide
  | closingPrice => decide
  | settlementPrice => decide
  | sessionHighPrice => decide
  | sessionLowPrice => decide
  | executionStatistics => decide
  | imbalance => decide
  | tradeVolume => decide
  | openInterest => decide
  | emptyBook => decide
  | securityTradingStatePhase => decide
  | priceBand => decide
  | quantityBand => decide
  | compositeUnderlyingPrice => decide
  | executionSummary => decide
  | volatilityPrice => decide
  | tradeBust => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MdEntryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MdEntryType

/-- Packet Header: 16 bytes -/
structure PacketHeader where
  channelId : BitVec 8
  reserved : BitVec 8
  sequenceVersion : BitVec 16
  sequenceNumber : BitVec 32
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace PacketHeader

def encode (message : PacketHeader) : List UInt8 :=
  encodeUInt 1 message.channelId
    ++ (encodeUInt 1 message.reserved
    ++ (encodeUIntLE 2 message.sequenceVersion
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 8 message.sendingTime))))

def decode (bytes : List UInt8) : Option (PacketHeader × List UInt8) := do
  let (channelId, bytes) ← decodeUInt 1 bytes
  let (reserved, bytes) ← decodeUInt 1 bytes
  let (sequenceVersion, bytes) ← decodeUIntLE 2 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ channelId, reserved, sequenceVersion, sequenceNumber, sendingTime }, bytes)

@[simp] theorem encode_length (message : PacketHeader) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : PacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PacketHeader) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end PacketHeader

/-- Sequence Reset Message: 0 bytes -/
structure SequenceResetMessage where
  deriving DecidableEq, Repr

namespace SequenceResetMessage

def encode (_ : SequenceResetMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SequenceResetMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SequenceResetMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SequenceResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end SequenceResetMessage

/-- Sequence Message: 4 bytes -/
structure SequenceMessage where
  nextSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceMessage

def encode (message : SequenceMessage) : List UInt8 :=
  encodeUIntLE 4 message.nextSeqNo

def decode (bytes : List UInt8) : Option (SequenceMessage × List UInt8) := do
  let (nextSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ nextSeqNo }, bytes)

@[simp] theorem encode_length (message : SequenceMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceMessage

/-- Empty Book Message: 20 bytes -/
structure EmptyBookMessage where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  offset9Padding3 : Alpha 3
  mdEntryTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace EmptyBookMessage

def encode (message : EmptyBookMessage) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.offset9Padding3
    ++ (encodeUIntLE 8 message.mdEntryTimestamp)))

def decode (bytes : List UInt8) : Option (EmptyBookMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (offset9Padding3, bytes) ← Alpha.decode 3 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, matchEventIndicator, offset9Padding3, mdEntryTimestamp }, bytes)

@[simp] theorem encode_length (message : EmptyBookMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : EmptyBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EmptyBookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EmptyBookMessage

/-- Channel Reset 11 Message: 12 bytes -/
structure ChannelReset11Message where
  matchEventIndicator : BitVec 8
  offset1Padding3 : Alpha 3
  mdEntryTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace ChannelReset11Message

def encode (message : ChannelReset11Message) : List UInt8 :=
  encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.offset1Padding3
    ++ (encodeUIntLE 8 message.mdEntryTimestamp))

def decode (bytes : List UInt8) : Option (ChannelReset11Message × List UInt8) := do
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (offset1Padding3, bytes) ← Alpha.decode 3 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ matchEventIndicator, offset1Padding3, mdEntryTimestamp }, bytes)

@[simp] theorem encode_length (message : ChannelReset11Message) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ChannelReset11Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ChannelReset11Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ChannelReset11Message

/-- Security Status 3 Message: 36 bytes -/
structure SecurityStatus3Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  tradingSessionId : BitVec 8
  securityTradingStatus : BitVec 8
  securityTradingEvent : BitVec 8
  tradeDate : BitVec 16
  offset14Padding2 : Alpha 2
  tradSesOpenTime : BitVec 64
  transactTime : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace SecurityStatus3Message

def encode (message : SecurityStatus3Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (encodeUInt 1 message.securityTradingStatus
    ++ (encodeUInt 1 message.securityTradingEvent
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (Alpha.encode message.offset14Padding2
    ++ (encodeUIntLE 8 message.tradSesOpenTime
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.rptSeq)))))))))

def decode (bytes : List UInt8) : Option (SecurityStatus3Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (securityTradingEvent, bytes) ← decodeUInt 1 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (offset14Padding2, bytes) ← Alpha.decode 2 bytes
  let (tradSesOpenTime, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, tradingSessionId, securityTradingStatus, securityTradingEvent, tradeDate, offset14Padding2, tradSesOpenTime, transactTime, rptSeq }, bytes)

@[simp] theorem encode_length (message : SecurityStatus3Message) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SecurityStatus3Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatus3Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityStatus3Message

/-- Security Group Phase 10 Message: 32 bytes -/
structure SecurityGroupPhase10Message where
  securityGroup : Alpha 3
  offset3Padding5 : Alpha 5
  matchEventIndicator : BitVec 8
  tradingSessionId : BitVec 8
  tradingSessionSubId : BitVec 8
  securityTradingEvent : BitVec 8
  tradeDate : BitVec 16
  offset14Padding2 : Alpha 2
  tradSesOpenTime : BitVec 64
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityGroupPhase10Message

def encode (message : SecurityGroupPhase10Message) : List UInt8 :=
  Alpha.encode message.securityGroup
    ++ (Alpha.encode message.offset3Padding5
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.securityTradingEvent
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (Alpha.encode message.offset14Padding2
    ++ (encodeUIntLE 8 message.tradSesOpenTime
    ++ (encodeUIntLE 8 message.transactTime)))))))))

def decode (bytes : List UInt8) : Option (SecurityGroupPhase10Message × List UInt8) := do
  let (securityGroup, bytes) ← Alpha.decode 3 bytes
  let (offset3Padding5, bytes) ← Alpha.decode 5 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (securityTradingEvent, bytes) ← decodeUInt 1 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (offset14Padding2, bytes) ← Alpha.decode 2 bytes
  let (tradSesOpenTime, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityGroup, offset3Padding5, matchEventIndicator, tradingSessionId, tradingSessionSubId, securityTradingEvent, tradeDate, offset14Padding2, tradSesOpenTime, transactTime }, bytes)

@[simp] theorem encode_length (message : SecurityGroupPhase10Message) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityGroupPhase10Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityGroupPhase10Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityGroupPhase10Message

/-- Maturity Month Year: 5 bytes -/
structure MaturityMonthYear where
  year : BitVec 16
  month : BitVec 8
  day : BitVec 8
  week : BitVec 8
  deriving DecidableEq, Repr

namespace MaturityMonthYear

def encode (message : MaturityMonthYear) : List UInt8 :=
  encodeUIntLE 2 message.year
    ++ (encodeUInt 1 message.month
    ++ (encodeUInt 1 message.day
    ++ (encodeUInt 1 message.week)))

def decode (bytes : List UInt8) : Option (MaturityMonthYear × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 2 bytes
  let (month, bytes) ← decodeUInt 1 bytes
  let (day, bytes) ← decodeUInt 1 bytes
  let (week, bytes) ← decodeUInt 1 bytes
  pure ({ year, month, day, week }, bytes)

@[simp] theorem encode_length (message : MaturityMonthYear) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MaturityMonthYear) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaturityMonthYear) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MaturityMonthYear

/-- Contract Settl Month: 5 bytes -/
structure ContractSettlMonth where
  year : BitVec 16
  month : BitVec 8
  day : BitVec 8
  week : BitVec 8
  deriving DecidableEq, Repr

namespace ContractSettlMonth

def encode (message : ContractSettlMonth) : List UInt8 :=
  encodeUIntLE 2 message.year
    ++ (encodeUInt 1 message.month
    ++ (encodeUInt 1 message.day
    ++ (encodeUInt 1 message.week)))

def decode (bytes : List UInt8) : Option (ContractSettlMonth × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 2 bytes
  let (month, bytes) ← decodeUInt 1 bytes
  let (day, bytes) ← decodeUInt 1 bytes
  let (week, bytes) ← decodeUInt 1 bytes
  pure ({ year, month, day, week }, bytes)

@[simp] theorem encode_length (message : ContractSettlMonth) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ContractSettlMonth) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractSettlMonth) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ContractSettlMonth

/-- Underlyings Group: 28 bytes -/
structure UnderlyingsGroup where
  underlyingSecurityId : BitVec 64
  underlyingSymbol : Alpha 20
  deriving DecidableEq, Repr

namespace UnderlyingsGroup

def encode (message : UnderlyingsGroup) : List UInt8 :=
  encodeUIntLE 8 message.underlyingSecurityId
    ++ (Alpha.encode message.underlyingSymbol)

def decode (bytes : List UInt8) : Option (UnderlyingsGroup × List UInt8) := do
  let (underlyingSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 20 bytes
  pure ({ underlyingSecurityId, underlyingSymbol }, bytes)

@[simp] theorem encode_length (message : UnderlyingsGroup) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : UnderlyingsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingsGroup

/-- Underlyings Groups -/
structure UnderlyingsGroups where
  blockLength : BitVec 16
  underlyingsGroup : Bounded 1 UnderlyingsGroup
  deriving DecidableEq, Repr

namespace UnderlyingsGroups

def encode (message : UnderlyingsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.underlyingsGroup.val.length)
    ++ (encodeMany UnderlyingsGroup.encode message.underlyingsGroup.val))

def decode (bytes : List UInt8) : Option (UnderlyingsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (underlyingsGroup_, bytes) ← decodeMany UnderlyingsGroup.decode numInGroup.toNat bytes
  if fits_underlyingsGroup : underlyingsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, underlyingsGroup := ⟨underlyingsGroup_, fits_underlyingsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : UnderlyingsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnderlyingsGroups) : (encode message).length ≤ 7143 := by
  have bound_underlyingsGroup := message.underlyingsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const UnderlyingsGroup.encode 28 UnderlyingsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : UnderlyingsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 UnderlyingsGroup.encode UnderlyingsGroup.decode UnderlyingsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.underlyingsGroup.length_lt]
  rfl

end UnderlyingsGroups

/-- Legs Group: 38 bytes -/
structure LegsGroup where
  legSecurityId : BitVec 64
  legRatioQty : BitVec 64
  legSecurityType : BitVec 8
  legSide : BitVec 8
  legSymbol : Alpha 20
  deriving DecidableEq, Repr

namespace LegsGroup

def encode (message : LegsGroup) : List UInt8 :=
  encodeUIntLE 8 message.legSecurityId
    ++ (encodeUIntLE 8 message.legRatioQty
    ++ (encodeUInt 1 message.legSecurityType
    ++ (encodeUInt 1 message.legSide
    ++ (Alpha.encode message.legSymbol))))

def decode (bytes : List UInt8) : Option (LegsGroup × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 8 bytes
  let (legSecurityType, bytes) ← decodeUInt 1 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (legSymbol, bytes) ← Alpha.decode 20 bytes
  pure ({ legSecurityId, legRatioQty, legSecurityType, legSide, legSymbol }, bytes)

@[simp] theorem encode_length (message : LegsGroup) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LegsGroup

/-- Legs Groups -/
structure LegsGroups where
  blockLength : BitVec 16
  legsGroup : Bounded 1 LegsGroup
  deriving DecidableEq, Repr

namespace LegsGroups

def encode (message : LegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legsGroup.val.length)
    ++ (encodeMany LegsGroup.encode message.legsGroup.val))

def decode (bytes : List UInt8) : Option (LegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (legsGroup_, bytes) ← decodeMany LegsGroup.decode numInGroup.toNat bytes
  if fits_legsGroup : legsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, legsGroup := ⟨legsGroup_, fits_legsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LegsGroups) : (encode message).length ≤ 9693 := by
  have bound_legsGroup := message.legsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const LegsGroup.encode 38 LegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegsGroup.encode LegsGroup.decode LegsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legsGroup.length_lt]
  rfl

end LegsGroups

/-- Instr Attribs Group: 2 bytes -/
structure InstrAttribsGroup where
  instrAttribType : BitVec 8
  instrAttribValue : BitVec 8
  deriving DecidableEq, Repr

namespace InstrAttribsGroup

def encode (message : InstrAttribsGroup) : List UInt8 :=
  encodeUInt 1 message.instrAttribType
    ++ (encodeUInt 1 message.instrAttribValue)

def decode (bytes : List UInt8) : Option (InstrAttribsGroup × List UInt8) := do
  let (instrAttribType, bytes) ← decodeUInt 1 bytes
  let (instrAttribValue, bytes) ← decodeUInt 1 bytes
  pure ({ instrAttribType, instrAttribValue }, bytes)

@[simp] theorem encode_length (message : InstrAttribsGroup) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : InstrAttribsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrAttribsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InstrAttribsGroup

/-- Instr Attribs Groups -/
structure InstrAttribsGroups where
  blockLength : BitVec 16
  instrAttribsGroup : Bounded 1 InstrAttribsGroup
  deriving DecidableEq, Repr

namespace InstrAttribsGroups

def encode (message : InstrAttribsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrAttribsGroup.val.length)
    ++ (encodeMany InstrAttribsGroup.encode message.instrAttribsGroup.val))

def decode (bytes : List UInt8) : Option (InstrAttribsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (instrAttribsGroup_, bytes) ← decodeMany InstrAttribsGroup.decode numInGroup.toNat bytes
  if fits_instrAttribsGroup : instrAttribsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, instrAttribsGroup := ⟨instrAttribsGroup_, fits_instrAttribsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : InstrAttribsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InstrAttribsGroups) : (encode message).length ≤ 513 := by
  have bound_instrAttribsGroup := message.instrAttribsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const InstrAttribsGroup.encode 2 InstrAttribsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : InstrAttribsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 InstrAttribsGroup.encode InstrAttribsGroup.decode InstrAttribsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.instrAttribsGroup.length_lt]
  rfl

end InstrAttribsGroups

/-- Security Desc -/
structure SecurityDesc where
  securityDescData : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace SecurityDesc

def encode (message : SecurityDesc) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityDescData.val.length)
    ++ (encodeMany Byte.encode message.securityDescData.val)

def decode (bytes : List UInt8) : Option (SecurityDesc × List UInt8) := do
  let (securityDescLength, bytes) ← decodeUInt 1 bytes
  let (securityDescData_, bytes) ← decodeMany Byte.decode securityDescLength.toNat bytes
  if fits_securityDescData : securityDescData_.length < 256 ^ 1 then
    pure ({ securityDescData := ⟨securityDescData_, fits_securityDescData⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityDesc) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDesc) : (encode message).length ≤ 256 := by
  have bound_securityDescData := message.securityDescData.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityDesc) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityDescData.length_lt]
  rfl

end SecurityDesc

/-- Security Definition Message -/
structure SecurityDefinitionMessage where
  securityId : BitVec 64
  securityExchange : Alpha 4
  securityIdSource : SecurityIdSource
  securityGroup : Alpha 3
  symbol : Alpha 20
  securityUpdateAction : SecurityUpdateAction
  securityType : BitVec 8
  securitySubType : BitVec 16
  totNoRelatedSym : BitVec 32
  minPriceIncrement : BitVec 64
  strikePrice : BitVec 64
  contractMultiplier : BitVec 64
  priceDivisor : BitVec 64
  securityValidityTimestamp : BitVec 64
  noSharesIssued : BitVec 64
  clearingHouseId : BitVec 64
  minOrderQty : BitVec 64
  maxOrderQty : BitVec 64
  minLotSize : BitVec 64
  minTradeVol : BitVec 64
  corporateActionEventId : BitVec 32
  issueDate : BitVec 32
  maturityDate : BitVec 32
  countryOfIssue : Alpha 2
  startDate : BitVec 32
  endDate : BitVec 32
  settlType : BitVec 16
  settlDate : BitVec 32
  datedDate : BitVec 32
  isinNumber : Alpha 12
  asset : Alpha 6
  cfiCode : Alpha 6
  maturityMonthYear : MaturityMonthYear
  contractSettlMonth : ContractSettlMonth
  currency : Alpha 3
  strikeCurrency : Alpha 3
  settlCurrency : Alpha 3
  securityStrategyType : Alpha 3
  lotType : BitVec 8
  tickSizeDenominator : BitVec 8
  product : BitVec 8
  exerciseStyle : BitVec 8
  putOrCall : BitVec 8
  priceTypeOptional : BitVec 8
  marketSegmentId : BitVec 8
  governanceIndicator : BitVec 8
  securityMatchType : BitVec 8
  lastFragment : BitVec 8
  multiLegModel : BitVec 8
  multiLegPriceMethod : BitVec 8
  minCrossQty : BitVec 64
  impliedMarketIndicator : BitVec 8
  underlyingsGroups : UnderlyingsGroups
  legsGroups : LegsGroups
  instrAttribsGroups : InstrAttribsGroups
  securityDesc : SecurityDesc
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessage

def encode (message : SecurityDefinitionMessage) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (Alpha.encode message.securityExchange
    ++ (SecurityIdSource.encode message.securityIdSource
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.symbol
    ++ (SecurityUpdateAction.encode message.securityUpdateAction
    ++ (encodeUInt 1 message.securityType
    ++ (encodeUIntLE 2 message.securitySubType
    ++ (encodeUIntLE 4 message.totNoRelatedSym
    ++ (encodeUIntLE 8 message.minPriceIncrement
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 8 message.contractMultiplier
    ++ (encodeUIntLE 8 message.priceDivisor
    ++ (encodeUIntLE 8 message.securityValidityTimestamp
    ++ (encodeUIntLE 8 message.noSharesIssued
    ++ (encodeUIntLE 8 message.clearingHouseId
    ++ (encodeUIntLE 8 message.minOrderQty
    ++ (encodeUIntLE 8 message.maxOrderQty
    ++ (encodeUIntLE 8 message.minLotSize
    ++ (encodeUIntLE 8 message.minTradeVol
    ++ (encodeUIntLE 4 message.corporateActionEventId
    ++ (encodeUIntLE 4 message.issueDate
    ++ (encodeUIntLE 4 message.maturityDate
    ++ (Alpha.encode message.countryOfIssue
    ++ (encodeUIntLE 4 message.startDate
    ++ (encodeUIntLE 4 message.endDate
    ++ (encodeUIntLE 2 message.settlType
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUIntLE 4 message.datedDate
    ++ (Alpha.encode message.isinNumber
    ++ (Alpha.encode message.asset
    ++ (Alpha.encode message.cfiCode
    ++ (MaturityMonthYear.encode message.maturityMonthYear
    ++ (ContractSettlMonth.encode message.contractSettlMonth
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.strikeCurrency
    ++ (Alpha.encode message.settlCurrency
    ++ (Alpha.encode message.securityStrategyType
    ++ (encodeUInt 1 message.lotType
    ++ (encodeUInt 1 message.tickSizeDenominator
    ++ (encodeUInt 1 message.product
    ++ (encodeUInt 1 message.exerciseStyle
    ++ (encodeUInt 1 message.putOrCall
    ++ (encodeUInt 1 message.priceTypeOptional
    ++ (encodeUInt 1 message.marketSegmentId
    ++ (encodeUInt 1 message.governanceIndicator
    ++ (encodeUInt 1 message.securityMatchType
    ++ (encodeUInt 1 message.lastFragment
    ++ (encodeUInt 1 message.multiLegModel
    ++ (encodeUInt 1 message.multiLegPriceMethod
    ++ (encodeUIntLE 8 message.minCrossQty
    ++ (encodeUInt 1 message.impliedMarketIndicator
    ++ (UnderlyingsGroups.encode message.underlyingsGroups
    ++ (LegsGroups.encode message.legsGroups
    ++ (InstrAttribsGroups.encode message.instrAttribsGroups
    ++ (SecurityDesc.encode message.securityDesc)))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecurityDefinitionMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (securityIdSource, bytes) ← SecurityIdSource.decode bytes
  let (securityGroup, bytes) ← Alpha.decode 3 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (securityUpdateAction, bytes) ← SecurityUpdateAction.decode bytes
  let (securityType, bytes) ← decodeUInt 1 bytes
  let (securitySubType, bytes) ← decodeUIntLE 2 bytes
  let (totNoRelatedSym, bytes) ← decodeUIntLE 4 bytes
  let (minPriceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (priceDivisor, bytes) ← decodeUIntLE 8 bytes
  let (securityValidityTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (noSharesIssued, bytes) ← decodeUIntLE 8 bytes
  let (clearingHouseId, bytes) ← decodeUIntLE 8 bytes
  let (minOrderQty, bytes) ← decodeUIntLE 8 bytes
  let (maxOrderQty, bytes) ← decodeUIntLE 8 bytes
  let (minLotSize, bytes) ← decodeUIntLE 8 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 8 bytes
  let (corporateActionEventId, bytes) ← decodeUIntLE 4 bytes
  let (issueDate, bytes) ← decodeUIntLE 4 bytes
  let (maturityDate, bytes) ← decodeUIntLE 4 bytes
  let (countryOfIssue, bytes) ← Alpha.decode 2 bytes
  let (startDate, bytes) ← decodeUIntLE 4 bytes
  let (endDate, bytes) ← decodeUIntLE 4 bytes
  let (settlType, bytes) ← decodeUIntLE 2 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (datedDate, bytes) ← decodeUIntLE 4 bytes
  let (isinNumber, bytes) ← Alpha.decode 12 bytes
  let (asset, bytes) ← Alpha.decode 6 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (contractSettlMonth, bytes) ← ContractSettlMonth.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (strikeCurrency, bytes) ← Alpha.decode 3 bytes
  let (settlCurrency, bytes) ← Alpha.decode 3 bytes
  let (securityStrategyType, bytes) ← Alpha.decode 3 bytes
  let (lotType, bytes) ← decodeUInt 1 bytes
  let (tickSizeDenominator, bytes) ← decodeUInt 1 bytes
  let (product, bytes) ← decodeUInt 1 bytes
  let (exerciseStyle, bytes) ← decodeUInt 1 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (priceTypeOptional, bytes) ← decodeUInt 1 bytes
  let (marketSegmentId, bytes) ← decodeUInt 1 bytes
  let (governanceIndicator, bytes) ← decodeUInt 1 bytes
  let (securityMatchType, bytes) ← decodeUInt 1 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (multiLegModel, bytes) ← decodeUInt 1 bytes
  let (multiLegPriceMethod, bytes) ← decodeUInt 1 bytes
  let (minCrossQty, bytes) ← decodeUIntLE 8 bytes
  let (impliedMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (underlyingsGroups, bytes) ← UnderlyingsGroups.decode bytes
  let (legsGroups, bytes) ← LegsGroups.decode bytes
  let (instrAttribsGroups, bytes) ← InstrAttribsGroups.decode bytes
  let (securityDesc, bytes) ← SecurityDesc.decode bytes
  pure ({ securityId, securityExchange, securityIdSource, securityGroup, symbol, securityUpdateAction, securityType, securitySubType, totNoRelatedSym, minPriceIncrement, strikePrice, contractMultiplier, priceDivisor, securityValidityTimestamp, noSharesIssued, clearingHouseId, minOrderQty, maxOrderQty, minLotSize, minTradeVol, corporateActionEventId, issueDate, maturityDate, countryOfIssue, startDate, endDate, settlType, settlDate, datedDate, isinNumber, asset, cfiCode, maturityMonthYear, contractSettlMonth, currency, strikeCurrency, settlCurrency, securityStrategyType, lotType, tickSizeDenominator, product, exerciseStyle, putOrCall, priceTypeOptional, marketSegmentId, governanceIndicator, securityMatchType, lastFragment, multiLegModel, multiLegPriceMethod, minCrossQty, impliedMarketIndicator, underlyingsGroups, legsGroups, instrAttribsGroups, securityDesc }, bytes)

theorem encode_length_pos (message : SecurityDefinitionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDefinitionMessage) : (encode message).length ≤ 17836 := by
  have bound_underlyingsGroups := UnderlyingsGroups.encode_length_le message.underlyingsGroups
  have bound_legsGroups := LegsGroups.encode_length_le message.legsGroups
  have bound_instrAttribsGroups := InstrAttribsGroups.encode_length_le message.instrAttribsGroups
  have bound_securityDesc := SecurityDesc.encode_length_le message.securityDesc
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, SecurityIdSource.encode_length, SecurityUpdateAction.encode_length, encodeUInt_length, MaturityMonthYear.encode_length, ContractSettlMonth.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecurityDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityIdSource.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityUpdateAction.decode_encode, some_bind]
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
  rw [List.append_assoc, MaturityMonthYear.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContractSettlMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, UnderlyingsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LegsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrAttribsGroups.decode_encode, some_bind]
  dsimp only
  rw [SecurityDesc.decode_encode, some_bind]
  rfl

end SecurityDefinitionMessage

/-- Headline -/
structure Headline where
  headlineData : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace Headline

def encode (message : Headline) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.headlineData.val.length)
    ++ (encodeMany Byte.encode message.headlineData.val)

def decode (bytes : List UInt8) : Option (Headline × List UInt8) := do
  let (headlineLength, bytes) ← decodeUIntLE 2 bytes
  let (headlineData_, bytes) ← decodeMany Byte.decode headlineLength.toNat bytes
  if fits_headlineData : headlineData_.length < 256 ^ 2 then
    pure ({ headlineData := ⟨headlineData_, fits_headlineData⟩ }, bytes)
  else none

theorem encode_length_pos (message : Headline) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Headline) : (encode message).length ≤ 65537 := by
  have bound_headlineData := message.headlineData.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : Headline) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.headlineData.length_lt]
  rfl

end Headline

/-- Text -/
structure Text where
  textData : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace Text

def encode (message : Text) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.textData.val.length)
    ++ (encodeMany Byte.encode message.textData.val)

def decode (bytes : List UInt8) : Option (Text × List UInt8) := do
  let (textLength, bytes) ← decodeUIntLE 2 bytes
  let (textData_, bytes) ← decodeMany Byte.decode textLength.toNat bytes
  if fits_textData : textData_.length < 256 ^ 2 then
    pure ({ textData := ⟨textData_, fits_textData⟩ }, bytes)
  else none

theorem encode_length_pos (message : Text) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Text) : (encode message).length ≤ 65537 := by
  have bound_textData := message.textData.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : Text) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.textData.length_lt]
  rfl

end Text

/-- Url Link -/
structure UrlLink where
  urlLinkData : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace UrlLink

def encode (message : UrlLink) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.urlLinkData.val.length)
    ++ (encodeMany Byte.encode message.urlLinkData.val)

def decode (bytes : List UInt8) : Option (UrlLink × List UInt8) := do
  let (urlLinkLength, bytes) ← decodeUIntLE 2 bytes
  let (urlLinkData_, bytes) ← decodeMany Byte.decode urlLinkLength.toNat bytes
  if fits_urlLinkData : urlLinkData_.length < 256 ^ 2 then
    pure ({ urlLinkData := ⟨urlLinkData_, fits_urlLinkData⟩ }, bytes)
  else none

theorem encode_length_pos (message : UrlLink) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UrlLink) : (encode message).length ≤ 65537 := by
  have bound_urlLinkData := message.urlLinkData.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : UrlLink) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.urlLinkData.length_lt]
  rfl

end UrlLink

/-- News 5 Message -/
structure News5Message where
  securityIdOptional : BitVec 64
  matchEventIndicator : BitVec 8
  newsSource : BitVec 8
  languageCode : Alpha 2
  partCount : BitVec 16
  partNumber : BitVec 16
  newsId : BitVec 64
  origTime : BitVec 64
  totalTextLength : BitVec 32
  headline : Headline
  text : Text
  urlLink : UrlLink
  deriving DecidableEq, Repr

namespace News5Message

def encode (message : News5Message) : List UInt8 :=
  encodeUIntLE 8 message.securityIdOptional
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.newsSource
    ++ (Alpha.encode message.languageCode
    ++ (encodeUIntLE 2 message.partCount
    ++ (encodeUIntLE 2 message.partNumber
    ++ (encodeUIntLE 8 message.newsId
    ++ (encodeUIntLE 8 message.origTime
    ++ (encodeUIntLE 4 message.totalTextLength
    ++ (Headline.encode message.headline
    ++ (Text.encode message.text
    ++ (UrlLink.encode message.urlLink)))))))))))

def decode (bytes : List UInt8) : Option (News5Message × List UInt8) := do
  let (securityIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (newsSource, bytes) ← decodeUInt 1 bytes
  let (languageCode, bytes) ← Alpha.decode 2 bytes
  let (partCount, bytes) ← decodeUIntLE 2 bytes
  let (partNumber, bytes) ← decodeUIntLE 2 bytes
  let (newsId, bytes) ← decodeUIntLE 8 bytes
  let (origTime, bytes) ← decodeUIntLE 8 bytes
  let (totalTextLength, bytes) ← decodeUIntLE 4 bytes
  let (headline, bytes) ← Headline.decode bytes
  let (text, bytes) ← Text.decode bytes
  let (urlLink, bytes) ← UrlLink.decode bytes
  pure ({ securityIdOptional, matchEventIndicator, newsSource, languageCode, partCount, partNumber, newsId, origTime, totalTextLength, headline, text, urlLink }, bytes)

theorem encode_length_pos (message : News5Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : News5Message) : (encode message).length ≤ 196647 := by
  have bound_headline := Headline.encode_length_le message.headline
  have bound_text := Text.encode_length_le message.text
  have bound_urlLink := UrlLink.encode_length_le message.urlLink
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : News5Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Headline.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Text.decode_encode, some_bind]
  dsimp only
  rw [UrlLink.decode_encode, some_bind]
  rfl

end News5Message

/-- Opening Price 15 Message: 44 bytes -/
structure OpeningPrice15Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  mdUpdateAction : BitVec 8
  openCloseSettlFlag : BitVec 8
  offset11Padding1 : Alpha 1
  mdFuturePrice : BitVec 64
  netChgPrevDay : BitVec 64
  tradeDate : BitVec 16
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  padding2 : Alpha 2
  deriving DecidableEq, Repr

namespace OpeningPrice15Message

def encode (message : OpeningPrice15Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (encodeUInt 1 message.openCloseSettlFlag
    ++ (Alpha.encode message.offset11Padding1
    ++ (encodeUIntLE 8 message.mdFuturePrice
    ++ (encodeUIntLE 8 message.netChgPrevDay
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (Alpha.encode message.padding2))))))))))

def decode (bytes : List UInt8) : Option (OpeningPrice15Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (offset11Padding1, bytes) ← Alpha.decode 1 bytes
  let (mdFuturePrice, bytes) ← decodeUIntLE 8 bytes
  let (netChgPrevDay, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  pure ({ securityId, matchEventIndicator, mdUpdateAction, openCloseSettlFlag, offset11Padding1, mdFuturePrice, netChgPrevDay, tradeDate, mdEntryTimestamp, rptSeq, padding2 }, bytes)

@[simp] theorem encode_length (message : OpeningPrice15Message) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OpeningPrice15Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpeningPrice15Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OpeningPrice15Message

/-- Theoretical Opening Price 16 Message: 40 bytes -/
structure TheoreticalOpeningPrice16Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  mdUpdateAction : BitVec 8
  tradeDate : BitVec 16
  mdCorporateOffsetPriceOptional : BitVec 64
  mdEntrySizeQuantityOptional : BitVec 64
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace TheoreticalOpeningPrice16Message

def encode (message : TheoreticalOpeningPrice16Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 8 message.mdCorporateOffsetPriceOptional
    ++ (encodeUIntLE 8 message.mdEntrySizeQuantityOptional
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq)))))))

def decode (bytes : List UInt8) : Option (TheoreticalOpeningPrice16Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (mdCorporateOffsetPriceOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeQuantityOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, mdUpdateAction, tradeDate, mdCorporateOffsetPriceOptional, mdEntrySizeQuantityOptional, mdEntryTimestamp, rptSeq }, bytes)

@[simp] theorem encode_length (message : TheoreticalOpeningPrice16Message) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TheoreticalOpeningPrice16Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TheoreticalOpeningPrice16Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

end TheoreticalOpeningPrice16Message

/-- Closing Price 17 Message: 36 bytes -/
structure ClosingPrice17Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  openCloseSettlFlag : BitVec 8
  offset10Padding2 : Alpha 2
  mdCorporatePrice : BitVec 64
  lastTradeDate : BitVec 16
  tradeDate : BitVec 16
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace ClosingPrice17Message

def encode (message : ClosingPrice17Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.openCloseSettlFlag
    ++ (Alpha.encode message.offset10Padding2
    ++ (encodeUIntLE 8 message.mdCorporatePrice
    ++ (encodeUIntLE 2 message.lastTradeDate
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq))))))))

def decode (bytes : List UInt8) : Option (ClosingPrice17Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (offset10Padding2, bytes) ← Alpha.decode 2 bytes
  let (mdCorporatePrice, bytes) ← decodeUIntLE 8 bytes
  let (lastTradeDate, bytes) ← decodeUIntLE 2 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, openCloseSettlFlag, offset10Padding2, mdCorporatePrice, lastTradeDate, tradeDate, mdEntryTimestamp, rptSeq }, bytes)

@[simp] theorem encode_length (message : ClosingPrice17Message) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ClosingPrice17Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClosingPrice17Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ClosingPrice17Message

/-- Auction Imbalance 19 Message: 32 bytes -/
structure AuctionImbalance19Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  mdUpdateAction : BitVec 8
  imbalanceCondition : BitVec 16
  mdEntrySizeQuantityOptional : BitVec 64
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace AuctionImbalance19Message

def encode (message : AuctionImbalance19Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (encodeUIntLE 2 message.imbalanceCondition
    ++ (encodeUIntLE 8 message.mdEntrySizeQuantityOptional
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq))))))

def decode (bytes : List UInt8) : Option (AuctionImbalance19Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (imbalanceCondition, bytes) ← decodeUIntLE 2 bytes
  let (mdEntrySizeQuantityOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, mdUpdateAction, imbalanceCondition, mdEntrySizeQuantityOptional, mdEntryTimestamp, rptSeq }, bytes)

@[simp] theorem encode_length (message : AuctionImbalance19Message) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : AuctionImbalance19Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionImbalance19Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AuctionImbalance19Message

/-- Quantity Band 21 Message: 40 bytes -/
structure QuantityBand21Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  offset9Padding3 : Alpha 3
  avgDailyTradedQty : BitVec 64
  maxTradeVol : BitVec 64
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace QuantityBand21Message

def encode (message : QuantityBand21Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.offset9Padding3
    ++ (encodeUIntLE 8 message.avgDailyTradedQty
    ++ (encodeUIntLE 8 message.maxTradeVol
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq))))))

def decode (bytes : List UInt8) : Option (QuantityBand21Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (offset9Padding3, bytes) ← Alpha.decode 3 bytes
  let (avgDailyTradedQty, bytes) ← decodeUIntLE 8 bytes
  let (maxTradeVol, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, offset9Padding3, avgDailyTradedQty, maxTradeVol, mdEntryTimestamp, rptSeq }, bytes)

@[simp] theorem encode_length (message : QuantityBand21Message) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : QuantityBand21Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuantityBand21Message) (rest : List UInt8) :
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

end QuantityBand21Message

/-- Price Band 22 Message: 48 bytes -/
structure PriceBand22Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  priceBandType : BitVec 8
  priceLimitType : BitVec 8
  priceBandMidpointPriceType : BitVec 8
  lowLimitPrice : BitVec 64
  highLimitPrice : BitVec 64
  tradingReferencePrice : BitVec 64
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace PriceBand22Message

def encode (message : PriceBand22Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.priceBandType
    ++ (encodeUInt 1 message.priceLimitType
    ++ (encodeUInt 1 message.priceBandMidpointPriceType
    ++ (encodeUIntLE 8 message.lowLimitPrice
    ++ (encodeUIntLE 8 message.highLimitPrice
    ++ (encodeUIntLE 8 message.tradingReferencePrice
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq)))))))))

def decode (bytes : List UInt8) : Option (PriceBand22Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (priceBandType, bytes) ← decodeUInt 1 bytes
  let (priceLimitType, bytes) ← decodeUInt 1 bytes
  let (priceBandMidpointPriceType, bytes) ← decodeUInt 1 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, priceBandType, priceLimitType, priceBandMidpointPriceType, lowLimitPrice, highLimitPrice, tradingReferencePrice, mdEntryTimestamp, rptSeq }, bytes)

@[simp] theorem encode_length (message : PriceBand22Message) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : PriceBand22Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceBand22Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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

end PriceBand22Message

/-- High Price 24 Message: 32 bytes -/
structure HighPrice24Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  mdUpdateAction : BitVec 8
  tradeDate : BitVec 16
  mdFuturePrice : BitVec 64
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace HighPrice24Message

def encode (message : HighPrice24Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 8 message.mdFuturePrice
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq))))))

def decode (bytes : List UInt8) : Option (HighPrice24Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (mdFuturePrice, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, mdUpdateAction, tradeDate, mdFuturePrice, mdEntryTimestamp, rptSeq }, bytes)

@[simp] theorem encode_length (message : HighPrice24Message) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : HighPrice24Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HighPrice24Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end HighPrice24Message

/-- Low Price 25 Message: 32 bytes -/
structure LowPrice25Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  mdUpdateAction : BitVec 8
  tradeDate : BitVec 16
  mdFuturePrice : BitVec 64
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace LowPrice25Message

def encode (message : LowPrice25Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 8 message.mdFuturePrice
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq))))))

def decode (bytes : List UInt8) : Option (LowPrice25Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (mdFuturePrice, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, mdUpdateAction, tradeDate, mdFuturePrice, mdEntryTimestamp, rptSeq }, bytes)

@[simp] theorem encode_length (message : LowPrice25Message) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LowPrice25Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LowPrice25Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LowPrice25Message

/-- Last Trade Price 27 Message: 68 bytes -/
structure LastTradePrice27Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  tradingSessionId : BitVec 8
  tradeCondition : BitVec 16
  mdFuturePrice : BitVec 64
  mdEntrySizeQuantity : BitVec 64
  tradeId : BitVec 32
  mdEntryBuyer : BitVec 32
  mdEntrySeller : BitVec 32
  tradeDate : BitVec 16
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  sellerDays : BitVec 16
  mdEntryInterestRate : BitVec 64
  trdSubType : BitVec 8
  padding3 : Alpha 3
  deriving DecidableEq, Repr

namespace LastTradePrice27Message

def encode (message : LastTradePrice27Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (encodeUIntLE 2 message.tradeCondition
    ++ (encodeUIntLE 8 message.mdFuturePrice
    ++ (encodeUIntLE 8 message.mdEntrySizeQuantity
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.mdEntryBuyer
    ++ (encodeUIntLE 4 message.mdEntrySeller
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUIntLE 2 message.sellerDays
    ++ (encodeUIntLE 8 message.mdEntryInterestRate
    ++ (encodeUInt 1 message.trdSubType
    ++ (Alpha.encode message.padding3)))))))))))))))

def decode (bytes : List UInt8) : Option (LastTradePrice27Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (tradeCondition, bytes) ← decodeUIntLE 2 bytes
  let (mdFuturePrice, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryBuyer, bytes) ← decodeUIntLE 4 bytes
  let (mdEntrySeller, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (sellerDays, bytes) ← decodeUIntLE 2 bytes
  let (mdEntryInterestRate, bytes) ← decodeUIntLE 8 bytes
  let (trdSubType, bytes) ← decodeUInt 1 bytes
  let (padding3, bytes) ← Alpha.decode 3 bytes
  pure ({ securityId, matchEventIndicator, tradingSessionId, tradeCondition, mdFuturePrice, mdEntrySizeQuantity, tradeId, mdEntryBuyer, mdEntrySeller, tradeDate, mdEntryTimestamp, rptSeq, sellerDays, mdEntryInterestRate, trdSubType, padding3 }, bytes)

@[simp] theorem encode_length (message : LastTradePrice27Message) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LastTradePrice27Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LastTradePrice27Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end LastTradePrice27Message

/-- Settlement Price 28 Message: 36 bytes -/
structure SettlementPrice28Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  offset9Padding1 : Alpha 1
  tradeDate : BitVec 16
  mdFuturePrice : BitVec 64
  mdEntryTimestamp : BitVec 64
  openCloseSettlFlag : BitVec 8
  priceType : BitVec 8
  settlPriceType : BitVec 8
  rptSeq : BitVec 32
  padding1 : Alpha 1
  deriving DecidableEq, Repr

namespace SettlementPrice28Message

def encode (message : SettlementPrice28Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.offset9Padding1
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 8 message.mdFuturePrice
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUInt 1 message.openCloseSettlFlag
    ++ (encodeUInt 1 message.priceType
    ++ (encodeUInt 1 message.settlPriceType
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (Alpha.encode message.padding1))))))))))

def decode (bytes : List UInt8) : Option (SettlementPrice28Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (offset9Padding1, bytes) ← Alpha.decode 1 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (mdFuturePrice, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (priceType, bytes) ← decodeUInt 1 bytes
  let (settlPriceType, bytes) ← decodeUInt 1 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (padding1, bytes) ← Alpha.decode 1 bytes
  pure ({ securityId, matchEventIndicator, offset9Padding1, tradeDate, mdFuturePrice, mdEntryTimestamp, openCloseSettlFlag, priceType, settlPriceType, rptSeq, padding1 }, bytes)

@[simp] theorem encode_length (message : SettlementPrice28Message) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SettlementPrice28Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SettlementPrice28Message) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SettlementPrice28Message

/-- Open Interest 29 Message: 32 bytes -/
structure OpenInterest29Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  offset9Padding1 : Alpha 1
  tradeDate : BitVec 16
  mdEntrySizeQuantity : BitVec 64
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace OpenInterest29Message

def encode (message : OpenInterest29Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.offset9Padding1
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 8 message.mdEntrySizeQuantity
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq))))))

def decode (bytes : List UInt8) : Option (OpenInterest29Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (offset9Padding1, bytes) ← Alpha.decode 1 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (mdEntrySizeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, offset9Padding1, tradeDate, mdEntrySizeQuantity, mdEntryTimestamp, rptSeq }, bytes)

@[simp] theorem encode_length (message : OpenInterest29Message) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OpenInterest29Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenInterest29Message) (rest : List UInt8) :
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

end OpenInterest29Message

/-- Snapshot Full Refresh Header 30 Message: 32 bytes -/
structure SnapshotFullRefreshHeader30Message where
  securityId : BitVec 64
  lastMsgSeqNumProcessed : BitVec 32
  totNumReports : BitVec 32
  totNumBids : BitVec 32
  totNumOffers : BitVec 32
  totNumStats : BitVec 16
  offset26Padding2 : Alpha 2
  lastRptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshHeader30Message

def encode (message : SnapshotFullRefreshHeader30Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.lastMsgSeqNumProcessed
    ++ (encodeUIntLE 4 message.totNumReports
    ++ (encodeUIntLE 4 message.totNumBids
    ++ (encodeUIntLE 4 message.totNumOffers
    ++ (encodeUIntLE 2 message.totNumStats
    ++ (Alpha.encode message.offset26Padding2
    ++ (encodeUIntLE 4 message.lastRptSeq)))))))

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshHeader30Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastMsgSeqNumProcessed, bytes) ← decodeUIntLE 4 bytes
  let (totNumReports, bytes) ← decodeUIntLE 4 bytes
  let (totNumBids, bytes) ← decodeUIntLE 4 bytes
  let (totNumOffers, bytes) ← decodeUIntLE 4 bytes
  let (totNumStats, bytes) ← decodeUIntLE 2 bytes
  let (offset26Padding2, bytes) ← Alpha.decode 2 bytes
  let (lastRptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, lastMsgSeqNumProcessed, totNumReports, totNumBids, totNumOffers, totNumStats, offset26Padding2, lastRptSeq }, bytes)

@[simp] theorem encode_length (message : SnapshotFullRefreshHeader30Message) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SnapshotFullRefreshHeader30Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotFullRefreshHeader30Message) (rest : List UInt8) :
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

end SnapshotFullRefreshHeader30Message

/-- Order Mb O 50 Message: 64 bytes -/
structure OrderMbO50Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  mdUpdateAction : BitVec 8
  mdEntryType : MdEntryType
  offset11Padding1 : Alpha 1
  mdCorporateOffsetPriceOptional : BitVec 64
  mdEntrySizeQuantity : BitVec 64
  mdEntryPositionNo : BitVec 32
  enteringFirm : BitVec 32
  mdInsertTimestamp : BitVec 64
  secondaryOrderId : BitVec 64
  rptSeq : BitVec 32
  mdEntryTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderMbO50Message

def encode (message : OrderMbO50Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (MdEntryType.encode message.mdEntryType
    ++ (Alpha.encode message.offset11Padding1
    ++ (encodeUIntLE 8 message.mdCorporateOffsetPriceOptional
    ++ (encodeUIntLE 8 message.mdEntrySizeQuantity
    ++ (encodeUIntLE 4 message.mdEntryPositionNo
    ++ (encodeUIntLE 4 message.enteringFirm
    ++ (encodeUIntLE 8 message.mdInsertTimestamp
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUIntLE 8 message.mdEntryTimestamp))))))))))))

def decode (bytes : List UInt8) : Option (OrderMbO50Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  let (offset11Padding1, bytes) ← Alpha.decode 1 bytes
  let (mdCorporateOffsetPriceOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryPositionNo, bytes) ← decodeUIntLE 4 bytes
  let (enteringFirm, bytes) ← decodeUIntLE 4 bytes
  let (mdInsertTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, matchEventIndicator, mdUpdateAction, mdEntryType, offset11Padding1, mdCorporateOffsetPriceOptional, mdEntrySizeQuantity, mdEntryPositionNo, enteringFirm, mdInsertTimestamp, secondaryOrderId, rptSeq, mdEntryTimestamp }, bytes)

@[simp] theorem encode_length (message : OrderMbO50Message) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderMbO50Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMbO50Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MdEntryType.decode_encode, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderMbO50Message

/-- Delete Order Mb O 51 Message: 44 bytes -/
structure DeleteOrderMbO51Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  offset9Padding1 : Alpha 1
  mdEntryType : MdEntryType
  offset11Padding1 : Alpha 1
  mdEntryPositionNo : BitVec 32
  mdEntrySizeQuantityOptional : BitVec 64
  secondaryOrderId : BitVec 64
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace DeleteOrderMbO51Message

def encode (message : DeleteOrderMbO51Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.offset9Padding1
    ++ (MdEntryType.encode message.mdEntryType
    ++ (Alpha.encode message.offset11Padding1
    ++ (encodeUIntLE 4 message.mdEntryPositionNo
    ++ (encodeUIntLE 8 message.mdEntrySizeQuantityOptional
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq)))))))))

def decode (bytes : List UInt8) : Option (DeleteOrderMbO51Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (offset9Padding1, bytes) ← Alpha.decode 1 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  let (offset11Padding1, bytes) ← Alpha.decode 1 bytes
  let (mdEntryPositionNo, bytes) ← decodeUIntLE 4 bytes
  let (mdEntrySizeQuantityOptional, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, offset9Padding1, mdEntryType, offset11Padding1, mdEntryPositionNo, mdEntrySizeQuantityOptional, secondaryOrderId, mdEntryTimestamp, rptSeq }, bytes)

@[simp] theorem encode_length (message : DeleteOrderMbO51Message) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, MdEntryType.encode_length]

theorem encode_length_pos (message : DeleteOrderMbO51Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderMbO51Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MdEntryType.decode_encode, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DeleteOrderMbO51Message

/-- Mass Delete Orders Mb O 52 Message: 28 bytes -/
structure MassDeleteOrdersMbO52Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  mdUpdateAction : BitVec 8
  mdEntryType : MdEntryType
  offset11Padding1 : Alpha 1
  mdEntryPositionNo : BitVec 32
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace MassDeleteOrdersMbO52Message

def encode (message : MassDeleteOrdersMbO52Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (MdEntryType.encode message.mdEntryType
    ++ (Alpha.encode message.offset11Padding1
    ++ (encodeUIntLE 4 message.mdEntryPositionNo
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq)))))))

def decode (bytes : List UInt8) : Option (MassDeleteOrdersMbO52Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  let (offset11Padding1, bytes) ← Alpha.decode 1 bytes
  let (mdEntryPositionNo, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, mdUpdateAction, mdEntryType, offset11Padding1, mdEntryPositionNo, mdEntryTimestamp, rptSeq }, bytes)

@[simp] theorem encode_length (message : MassDeleteOrdersMbO52Message) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : MassDeleteOrdersMbO52Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassDeleteOrdersMbO52Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MdEntryType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MassDeleteOrdersMbO52Message

/-- Trade 53 Message: 56 bytes -/
structure Trade53Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  tradingSessionId : BitVec 8
  tradeCondition : BitVec 16
  mdFuturePrice : BitVec 64
  mdEntrySizeQuantity : BitVec 64
  tradeId : BitVec 32
  mdEntryBuyer : BitVec 32
  mdEntrySeller : BitVec 32
  tradeDate : BitVec 16
  trdSubType : BitVec 8
  offset43Padding1 : Alpha 1
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace Trade53Message

def encode (message : Trade53Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (encodeUIntLE 2 message.tradeCondition
    ++ (encodeUIntLE 8 message.mdFuturePrice
    ++ (encodeUIntLE 8 message.mdEntrySizeQuantity
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.mdEntryBuyer
    ++ (encodeUIntLE 4 message.mdEntrySeller
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUInt 1 message.trdSubType
    ++ (Alpha.encode message.offset43Padding1
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq)))))))))))))

def decode (bytes : List UInt8) : Option (Trade53Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (tradeCondition, bytes) ← decodeUIntLE 2 bytes
  let (mdFuturePrice, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryBuyer, bytes) ← decodeUIntLE 4 bytes
  let (mdEntrySeller, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (trdSubType, bytes) ← decodeUInt 1 bytes
  let (offset43Padding1, bytes) ← Alpha.decode 1 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, tradingSessionId, tradeCondition, mdFuturePrice, mdEntrySizeQuantity, tradeId, mdEntryBuyer, mdEntrySeller, tradeDate, trdSubType, offset43Padding1, mdEntryTimestamp, rptSeq }, bytes)

@[simp] theorem encode_length (message : Trade53Message) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : Trade53Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Trade53Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end Trade53Message

/-- Forward Trade 54 Message: 68 bytes -/
structure ForwardTrade54Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  tradingSessionId : BitVec 8
  tradeCondition : BitVec 16
  mdFuturePrice : BitVec 64
  mdEntrySizeQuantity : BitVec 64
  tradeId : BitVec 32
  mdEntryBuyer : BitVec 32
  mdEntrySeller : BitVec 32
  tradeDate : BitVec 16
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  sellerDays : BitVec 16
  mdEntryInterestRate : BitVec 64
  trdSubType : BitVec 8
  padding3 : Alpha 3
  deriving DecidableEq, Repr

namespace ForwardTrade54Message

def encode (message : ForwardTrade54Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (encodeUIntLE 2 message.tradeCondition
    ++ (encodeUIntLE 8 message.mdFuturePrice
    ++ (encodeUIntLE 8 message.mdEntrySizeQuantity
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.mdEntryBuyer
    ++ (encodeUIntLE 4 message.mdEntrySeller
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUIntLE 2 message.sellerDays
    ++ (encodeUIntLE 8 message.mdEntryInterestRate
    ++ (encodeUInt 1 message.trdSubType
    ++ (Alpha.encode message.padding3)))))))))))))))

def decode (bytes : List UInt8) : Option (ForwardTrade54Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (tradeCondition, bytes) ← decodeUIntLE 2 bytes
  let (mdFuturePrice, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryBuyer, bytes) ← decodeUIntLE 4 bytes
  let (mdEntrySeller, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (sellerDays, bytes) ← decodeUIntLE 2 bytes
  let (mdEntryInterestRate, bytes) ← decodeUIntLE 8 bytes
  let (trdSubType, bytes) ← decodeUInt 1 bytes
  let (padding3, bytes) ← Alpha.decode 3 bytes
  pure ({ securityId, matchEventIndicator, tradingSessionId, tradeCondition, mdFuturePrice, mdEntrySizeQuantity, tradeId, mdEntryBuyer, mdEntrySeller, tradeDate, mdEntryTimestamp, rptSeq, sellerDays, mdEntryInterestRate, trdSubType, padding3 }, bytes)

@[simp] theorem encode_length (message : ForwardTrade54Message) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ForwardTrade54Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ForwardTrade54Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ForwardTrade54Message

/-- Execution Summary 55 Message: 64 bytes -/
structure ExecutionSummary55Message where
  securityId : BitVec 64
  offset8Padding2 : Alpha 2
  aggressorSide : BitVec 8
  offset11Padding1 : Alpha 1
  lastPx : BitVec 64
  fillQty : BitVec 64
  tradedHiddenQty : BitVec 64
  cxlQty : BitVec 64
  aggressorTime : BitVec 64
  rptSeq : BitVec 32
  mdEntryTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionSummary55Message

def encode (message : ExecutionSummary55Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (Alpha.encode message.offset8Padding2
    ++ (encodeUInt 1 message.aggressorSide
    ++ (Alpha.encode message.offset11Padding1
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.fillQty
    ++ (encodeUIntLE 8 message.tradedHiddenQty
    ++ (encodeUIntLE 8 message.cxlQty
    ++ (encodeUIntLE 8 message.aggressorTime
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUIntLE 8 message.mdEntryTimestamp))))))))))

def decode (bytes : List UInt8) : Option (ExecutionSummary55Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (offset8Padding2, bytes) ← Alpha.decode 2 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (offset11Padding1, bytes) ← Alpha.decode 1 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← decodeUIntLE 8 bytes
  let (tradedHiddenQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (aggressorTime, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, offset8Padding2, aggressorSide, offset11Padding1, lastPx, fillQty, tradedHiddenQty, cxlQty, aggressorTime, rptSeq, mdEntryTimestamp }, bytes)

@[simp] theorem encode_length (message : ExecutionSummary55Message) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ExecutionSummary55Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionSummary55Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExecutionSummary55Message

/-- Execution Statistics 56 Message: 52 bytes -/
structure ExecutionStatistics56Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  tradingSessionId : BitVec 8
  tradeDate : BitVec 16
  tradeVolume : BitVec 64
  vwapPx : BitVec 64
  netChgPrevDay : BitVec 64
  numberOfTrades : BitVec 32
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace ExecutionStatistics56Message

def encode (message : ExecutionStatistics56Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 8 message.tradeVolume
    ++ (encodeUIntLE 8 message.vwapPx
    ++ (encodeUIntLE 8 message.netChgPrevDay
    ++ (encodeUIntLE 4 message.numberOfTrades
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq)))))))))

def decode (bytes : List UInt8) : Option (ExecutionStatistics56Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (tradeVolume, bytes) ← decodeUIntLE 8 bytes
  let (vwapPx, bytes) ← decodeUIntLE 8 bytes
  let (netChgPrevDay, bytes) ← decodeUIntLE 8 bytes
  let (numberOfTrades, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, tradingSessionId, tradeDate, tradeVolume, vwapPx, netChgPrevDay, numberOfTrades, mdEntryTimestamp, rptSeq }, bytes)

@[simp] theorem encode_length (message : ExecutionStatistics56Message) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ExecutionStatistics56Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionStatistics56Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExecutionStatistics56Message

/-- Trade Bust 57 Message: 48 bytes -/
structure TradeBust57Message where
  securityId : BitVec 64
  matchEventIndicator : BitVec 8
  tradingSessionId : BitVec 8
  offset10Padding2 : Alpha 2
  mdFuturePrice : BitVec 64
  mdEntrySizeQuantity : BitVec 64
  tradeId : BitVec 32
  tradeDate : BitVec 16
  offset34Padding2 : Alpha 2
  mdEntryTimestamp : BitVec 64
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace TradeBust57Message

def encode (message : TradeBust57Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (Alpha.encode message.offset10Padding2
    ++ (encodeUIntLE 8 message.mdFuturePrice
    ++ (encodeUIntLE 8 message.mdEntrySizeQuantity
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (Alpha.encode message.offset34Padding2
    ++ (encodeUIntLE 8 message.mdEntryTimestamp
    ++ (encodeUIntLE 4 message.rptSeq))))))))))

def decode (bytes : List UInt8) : Option (TradeBust57Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (offset10Padding2, bytes) ← Alpha.decode 2 bytes
  let (mdFuturePrice, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (offset34Padding2, bytes) ← Alpha.decode 2 bytes
  let (mdEntryTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, matchEventIndicator, tradingSessionId, offset10Padding2, mdFuturePrice, mdEntrySizeQuantity, tradeId, tradeDate, offset34Padding2, mdEntryTimestamp, rptSeq }, bytes)

@[simp] theorem encode_length (message : TradeBust57Message) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeBust57Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBust57Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeBust57Message

/-- Snapshot Full Refresh Orders Mb O 71 Message no M D Entries Group: 42 bytes -/
structure SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup where
  mdCorporateOffsetPriceOptional : BitVec 64
  mdEntrySizeQuantity : BitVec 64
  mdEntryPositionNo : BitVec 32
  enteringFirm : BitVec 32
  mdInsertTimestamp : BitVec 64
  secondaryOrderId : BitVec 64
  mdEntryType : MdEntryType
  matchEventIndicatorOptional : BitVec 8
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup

def encode (message : SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdCorporateOffsetPriceOptional
    ++ (encodeUIntLE 8 message.mdEntrySizeQuantity
    ++ (encodeUIntLE 4 message.mdEntryPositionNo
    ++ (encodeUIntLE 4 message.enteringFirm
    ++ (encodeUIntLE 8 message.mdInsertTimestamp
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (MdEntryType.encode message.mdEntryType
    ++ (encodeUIntLE 1 message.matchEventIndicatorOptional)))))))

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup × List UInt8) := do
  let (mdCorporateOffsetPriceOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryPositionNo, bytes) ← decodeUIntLE 4 bytes
  let (enteringFirm, bytes) ← decodeUIntLE 4 bytes
  let (mdInsertTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  let (matchEventIndicatorOptional, bytes) ← decodeUIntLE 1 bytes
  pure ({ mdCorporateOffsetPriceOptional, mdEntrySizeQuantity, mdEntryPositionNo, enteringFirm, mdInsertTimestamp, secondaryOrderId, mdEntryType, matchEventIndicatorOptional }, bytes)

@[simp] theorem encode_length (message : SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MdEntryType.encode_length]

theorem encode_length_pos (message : SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, MdEntryType.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup

/-- Snapshot Full Refresh Orders Mb O 71 Message no M D Entries Groups -/
structure SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups where
  blockLength : BitVec 16
  snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup : Bounded 1 SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups

def encode (message : SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup.val.length)
    ++ (encodeMany SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup.encode message.snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup.val))

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup_, bytes) ← decodeMany SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup.decode numInGroup.toNat bytes
  if fits_snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup : snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup := ⟨snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup_, fits_snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups) : (encode message).length ≤ 10713 := by
  have bound_snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup := message.snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup.encode 42 SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup.encode SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup.decode SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroup.length_lt]
  rfl

end SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups

/-- Snapshot Full Refresh Orders Mb O 71 Message -/
structure SnapshotFullRefreshOrdersMbO71Message where
  securityId : BitVec 64
  snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups : SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshOrdersMbO71Message

def encode (message : SnapshotFullRefreshOrdersMbO71Message) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups.encode message.snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups)

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshOrdersMbO71Message × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups, bytes) ← SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups.decode bytes
  pure ({ securityId, snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups }, bytes)

theorem encode_length_pos (message : SnapshotFullRefreshOrdersMbO71Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotFullRefreshOrdersMbO71Message) : (encode message).length ≤ 10721 := by
  have bound_snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups := SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups.encode_length_le message.snapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : SnapshotFullRefreshOrdersMbO71Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [SnapshotFullRefreshOrdersMbO71MessageNoMDEntriesGroups.decode_encode, some_bind]
  rfl

end SnapshotFullRefreshOrdersMbO71Message

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | sequenceResetMessage (message : SequenceResetMessage) -- 1
  | sequenceMessage (message : SequenceMessage) -- 2
  | emptyBookMessage (message : EmptyBookMessage) -- 9
  | channelReset11Message (message : ChannelReset11Message) -- 11
  | securityStatus3Message (message : SecurityStatus3Message) -- 3
  | securityGroupPhase10Message (message : SecurityGroupPhase10Message) -- 10
  | securityDefinitionMessage (message : SecurityDefinitionMessage) -- 12
  | news5Message (message : News5Message) -- 5
  | openingPrice15Message (message : OpeningPrice15Message) -- 15
  | theoreticalOpeningPrice16Message (message : TheoreticalOpeningPrice16Message) -- 16
  | closingPrice17Message (message : ClosingPrice17Message) -- 17
  | auctionImbalance19Message (message : AuctionImbalance19Message) -- 19
  | quantityBand21Message (message : QuantityBand21Message) -- 21
  | priceBand22Message (message : PriceBand22Message) -- 22
  | highPrice24Message (message : HighPrice24Message) -- 24
  | lowPrice25Message (message : LowPrice25Message) -- 25
  | lastTradePrice27Message (message : LastTradePrice27Message) -- 27
  | settlementPrice28Message (message : SettlementPrice28Message) -- 28
  | openInterest29Message (message : OpenInterest29Message) -- 29
  | snapshotFullRefreshHeader30Message (message : SnapshotFullRefreshHeader30Message) -- 30
  | orderMbO50Message (message : OrderMbO50Message) -- 50
  | deleteOrderMbO51Message (message : DeleteOrderMbO51Message) -- 51
  | massDeleteOrdersMbO52Message (message : MassDeleteOrdersMbO52Message) -- 52
  | trade53Message (message : Trade53Message) -- 53
  | forwardTrade54Message (message : ForwardTrade54Message) -- 54
  | executionSummary55Message (message : ExecutionSummary55Message) -- 55
  | executionStatistics56Message (message : ExecutionStatistics56Message) -- 56
  | tradeBust57Message (message : TradeBust57Message) -- 57
  | snapshotFullRefreshOrdersMbO71Message (message : SnapshotFullRefreshOrdersMbO71Message) -- 71
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceResetMessage _ => 1
  | .sequenceMessage _ => 2
  | .emptyBookMessage _ => 9
  | .channelReset11Message _ => 11
  | .securityStatus3Message _ => 3
  | .securityGroupPhase10Message _ => 10
  | .securityDefinitionMessage _ => 12
  | .news5Message _ => 5
  | .openingPrice15Message _ => 15
  | .theoreticalOpeningPrice16Message _ => 16
  | .closingPrice17Message _ => 17
  | .auctionImbalance19Message _ => 19
  | .quantityBand21Message _ => 21
  | .priceBand22Message _ => 22
  | .highPrice24Message _ => 24
  | .lowPrice25Message _ => 25
  | .lastTradePrice27Message _ => 27
  | .settlementPrice28Message _ => 28
  | .openInterest29Message _ => 29
  | .snapshotFullRefreshHeader30Message _ => 30
  | .orderMbO50Message _ => 50
  | .deleteOrderMbO51Message _ => 51
  | .massDeleteOrdersMbO52Message _ => 52
  | .trade53Message _ => 53
  | .forwardTrade54Message _ => 54
  | .executionSummary55Message _ => 55
  | .executionStatistics56Message _ => 56
  | .tradeBust57Message _ => 57
  | .snapshotFullRefreshOrdersMbO71Message _ => 71

def encode : Payload → List UInt8
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .sequenceMessage message => SequenceMessage.encode message
  | .emptyBookMessage message => EmptyBookMessage.encode message
  | .channelReset11Message message => ChannelReset11Message.encode message
  | .securityStatus3Message message => SecurityStatus3Message.encode message
  | .securityGroupPhase10Message message => SecurityGroupPhase10Message.encode message
  | .securityDefinitionMessage message => SecurityDefinitionMessage.encode message
  | .news5Message message => News5Message.encode message
  | .openingPrice15Message message => OpeningPrice15Message.encode message
  | .theoreticalOpeningPrice16Message message => TheoreticalOpeningPrice16Message.encode message
  | .closingPrice17Message message => ClosingPrice17Message.encode message
  | .auctionImbalance19Message message => AuctionImbalance19Message.encode message
  | .quantityBand21Message message => QuantityBand21Message.encode message
  | .priceBand22Message message => PriceBand22Message.encode message
  | .highPrice24Message message => HighPrice24Message.encode message
  | .lowPrice25Message message => LowPrice25Message.encode message
  | .lastTradePrice27Message message => LastTradePrice27Message.encode message
  | .settlementPrice28Message message => SettlementPrice28Message.encode message
  | .openInterest29Message message => OpenInterest29Message.encode message
  | .snapshotFullRefreshHeader30Message message => SnapshotFullRefreshHeader30Message.encode message
  | .orderMbO50Message message => OrderMbO50Message.encode message
  | .deleteOrderMbO51Message message => DeleteOrderMbO51Message.encode message
  | .massDeleteOrdersMbO52Message message => MassDeleteOrdersMbO52Message.encode message
  | .trade53Message message => Trade53Message.encode message
  | .forwardTrade54Message message => ForwardTrade54Message.encode message
  | .executionSummary55Message message => ExecutionSummary55Message.encode message
  | .executionStatistics56Message message => ExecutionStatistics56Message.encode message
  | .tradeBust57Message message => TradeBust57Message.encode message
  | .snapshotFullRefreshOrdersMbO71Message message => SnapshotFullRefreshOrdersMbO71Message.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 2 then (SequenceMessage.decode bytes).map fun (message, rest) => (.sequenceMessage message, rest)
  else if tag = 9 then (EmptyBookMessage.decode bytes).map fun (message, rest) => (.emptyBookMessage message, rest)
  else if tag = 11 then (ChannelReset11Message.decode bytes).map fun (message, rest) => (.channelReset11Message message, rest)
  else if tag = 3 then (SecurityStatus3Message.decode bytes).map fun (message, rest) => (.securityStatus3Message message, rest)
  else if tag = 10 then (SecurityGroupPhase10Message.decode bytes).map fun (message, rest) => (.securityGroupPhase10Message message, rest)
  else if tag = 12 then (SecurityDefinitionMessage.decode bytes).map fun (message, rest) => (.securityDefinitionMessage message, rest)
  else if tag = 5 then (News5Message.decode bytes).map fun (message, rest) => (.news5Message message, rest)
  else if tag = 15 then (OpeningPrice15Message.decode bytes).map fun (message, rest) => (.openingPrice15Message message, rest)
  else if tag = 16 then (TheoreticalOpeningPrice16Message.decode bytes).map fun (message, rest) => (.theoreticalOpeningPrice16Message message, rest)
  else if tag = 17 then (ClosingPrice17Message.decode bytes).map fun (message, rest) => (.closingPrice17Message message, rest)
  else if tag = 19 then (AuctionImbalance19Message.decode bytes).map fun (message, rest) => (.auctionImbalance19Message message, rest)
  else if tag = 21 then (QuantityBand21Message.decode bytes).map fun (message, rest) => (.quantityBand21Message message, rest)
  else if tag = 22 then (PriceBand22Message.decode bytes).map fun (message, rest) => (.priceBand22Message message, rest)
  else if tag = 24 then (HighPrice24Message.decode bytes).map fun (message, rest) => (.highPrice24Message message, rest)
  else if tag = 25 then (LowPrice25Message.decode bytes).map fun (message, rest) => (.lowPrice25Message message, rest)
  else if tag = 27 then (LastTradePrice27Message.decode bytes).map fun (message, rest) => (.lastTradePrice27Message message, rest)
  else if tag = 28 then (SettlementPrice28Message.decode bytes).map fun (message, rest) => (.settlementPrice28Message message, rest)
  else if tag = 29 then (OpenInterest29Message.decode bytes).map fun (message, rest) => (.openInterest29Message message, rest)
  else if tag = 30 then (SnapshotFullRefreshHeader30Message.decode bytes).map fun (message, rest) => (.snapshotFullRefreshHeader30Message message, rest)
  else if tag = 50 then (OrderMbO50Message.decode bytes).map fun (message, rest) => (.orderMbO50Message message, rest)
  else if tag = 51 then (DeleteOrderMbO51Message.decode bytes).map fun (message, rest) => (.deleteOrderMbO51Message message, rest)
  else if tag = 52 then (MassDeleteOrdersMbO52Message.decode bytes).map fun (message, rest) => (.massDeleteOrdersMbO52Message message, rest)
  else if tag = 53 then (Trade53Message.decode bytes).map fun (message, rest) => (.trade53Message message, rest)
  else if tag = 54 then (ForwardTrade54Message.decode bytes).map fun (message, rest) => (.forwardTrade54Message message, rest)
  else if tag = 55 then (ExecutionSummary55Message.decode bytes).map fun (message, rest) => (.executionSummary55Message message, rest)
  else if tag = 56 then (ExecutionStatistics56Message.decode bytes).map fun (message, rest) => (.executionStatistics56Message message, rest)
  else if tag = 57 then (TradeBust57Message.decode bytes).map fun (message, rest) => (.tradeBust57Message message, rest)
  else if tag = 71 then (SnapshotFullRefreshOrdersMbO71Message.decode bytes).map fun (message, rest) => (.snapshotFullRefreshOrdersMbO71Message message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  encodingType : BitVec 16
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.encodingType
    ++ (encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload)))))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (encodingType, bytes) ← decodeUIntLE 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ encodingType, blockLength, schemaId, version, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
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
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Size rule: Message Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  packetHeader : PacketHeader
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  PacketHeader.encode message.packetHeader
    ++ (encodeMany Message.encode message.message)

def decode (bytes : List UInt8) : Option Packet := do
  let (packetHeader, bytes) ← PacketHeader.decode bytes
  let message ← decodeAll Message.decode bytes.length bytes
  pure { packetHeader, message }

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [PacketHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [PacketHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end Packet

end Omi.B3B3derivativesBinaryumdfSbeV19
