import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Ise Top Combo Quote Feed v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqIseoptionsTopcomboquotefeedItchV10

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4E, 0x4C, 0x45, 0x43, 0x57]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfOpeningProcess -- Start Of Opening Process
  | startOfNormalHoursClosingProcess -- Start Of Normal Hours Closing Process
  | startOfLateHoursClosingProcess -- Start Of Late Hours Closing Process
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | endOfWcoEarlyClosing -- End Of Wco Early Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfOpeningProcess => 0x51
  | .startOfNormalHoursClosingProcess => 0x4E
  | .startOfLateHoursClosingProcess => 0x4C
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .endOfWcoEarlyClosing => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfOpeningProcess
  else if byte = 0x4E then .startOfNormalHoursClosingProcess
  else if byte = 0x4C then .startOfLateHoursClosingProcess
  else if byte = 0x45 then .endOfSystemHours
  else if byte = 0x43 then .endOfMessages
  else .endOfWcoEarlyClosing

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfOpeningProcess => decide
  | startOfNormalHoursClosingProcess => decide
  | startOfLateHoursClosingProcess => decide
  | endOfSystemHours => decide
  | endOfMessages => decide
  | endOfWcoEarlyClosing => decide
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

/-- Strategy Type: one byte code -/
def StrategyType.codes : List UInt8 :=
  [0x56, 0x54, 0x44, 0x53, 0x47, 0x43, 0x52, 0x41, 0x55]

inductive StrategyType where
  | verticalSpread -- Vertical Spread
  | timeSpread -- Time Spread
  | diagonalSpread -- Diagonal Spread
  | straddle -- Straddle
  | strangle -- Strangle
  | combo -- Combo
  | riskReversal -- Risk Reversal
  | ratioSpread -- Ratio Spread
  | custom -- Custom
  | unlisted (byte : { byte : UInt8 // byte ∉ StrategyType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrategyType

def toByte : StrategyType → UInt8
  | .verticalSpread => 0x56
  | .timeSpread => 0x54
  | .diagonalSpread => 0x44
  | .straddle => 0x53
  | .strangle => 0x47
  | .combo => 0x43
  | .riskReversal => 0x52
  | .ratioSpread => 0x41
  | .custom => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrategyType :=
  if byte = 0x56 then .verticalSpread
  else if byte = 0x54 then .timeSpread
  else if byte = 0x44 then .diagonalSpread
  else if byte = 0x53 then .straddle
  else if byte = 0x47 then .strangle
  else if byte = 0x43 then .combo
  else if byte = 0x52 then .riskReversal
  else if byte = 0x41 then .ratioSpread
  else .custom

def ofByte (byte : UInt8) : StrategyType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrategyType) : ofByte value.toByte = value := by
  cases value with
  | verticalSpread => decide
  | timeSpread => decide
  | diagonalSpread => decide
  | straddle => decide
  | strangle => decide
  | combo => decide
  | riskReversal => decide
  | ratioSpread => decide
  | custom => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrategyType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrategyType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrategyType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StrategyType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrategyType

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x43, 0x50]

inductive OptionType where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionType

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

/-- Open State: one byte code -/
def OpenState.codes : List UInt8 :=
  [0x59, 0x4E]

inductive OpenState where
  | open_ -- Open
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenState

def toByte : OpenState → UInt8
  | .open_ => 0x59
  | .closed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenState :=
  if byte = 0x59 then .open_
  else .closed

def ofByte (byte : UInt8) : OpenState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenState) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | closed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenState

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x48, 0x54]

inductive CurrentTradingState where
  | haltInEffect -- Halt In Effect
  | tradingResumed -- Trading Resumed
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .haltInEffect => 0x48
  | .tradingResumed => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .haltInEffect
  else .tradingResumed

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | haltInEffect => decide
  | tradingResumed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CurrentTradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CurrentTradingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CurrentTradingState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CurrentTradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CurrentTradingState

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x58]

inductive QuoteCondition where
  | halted -- Halted
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .halted => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : QuoteCondition :=
  .halted

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
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

/-- System Event Message: 13 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 48
  eventCode : EventCode
  currentYear : BitVec 16
  currentMonth : BitVec 8
  currentDay : BitVec 8
  version : BitVec 8
  subversion : BitVec 8
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 2 message.currentYear
    ++ (encodeUInt 1 message.currentMonth
    ++ (encodeUInt 1 message.currentDay
    ++ (encodeUInt 1 message.version
    ++ (encodeUInt 1 message.subversion))))))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (currentYear, bytes) ← decodeUInt 2 bytes
  let (currentMonth, bytes) ← decodeUInt 1 bytes
  let (currentDay, bytes) ← decodeUInt 1 bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (subversion, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, eventCode, currentYear, currentMonth, currentDay, version, subversion }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
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

end SystemEventMessage

/-- Leg Information: 28 bytes -/
structure LegInformation where
  optionId : BitVec 32
  securitySymbol : Alpha 6
  legId : BitVec 8
  expirationYear : BitVec 8
  expirationMonth : BitVec 8
  expirationDay : BitVec 8
  explicitStrikePrice : BitVec 64
  optionType : OptionType
  side : Side
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace LegInformation

def encode (message : LegInformation) : List UInt8 :=
  encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 1 message.legId
    ++ (encodeUInt 1 message.expirationYear
    ++ (encodeUInt 1 message.expirationMonth
    ++ (encodeUInt 1 message.expirationDay
    ++ (encodeUInt 8 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.legRatio)))))))))

def decode (bytes : List UInt8) : Option (LegInformation × List UInt8) := do
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 6 bytes
  let (legId, bytes) ← decodeUInt 1 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  let (expirationMonth, bytes) ← decodeUInt 1 bytes
  let (expirationDay, bytes) ← decodeUInt 1 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 8 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (legRatio, bytes) ← decodeUInt 4 bytes
  pure ({ optionId, securitySymbol, legId, expirationYear, expirationMonth, expirationDay, explicitStrikePrice, optionType, side, legRatio }, bytes)

@[simp] theorem encode_length (message : LegInformation) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, Side.encode_length]

theorem encode_length_pos (message : LegInformation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegInformation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LegInformation

/-- Complex Strategy Directory Message -/
structure ComplexStrategyDirectoryMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  strategyType : StrategyType
  source : BitVec 8
  underlyingSymbol : Alpha 13
  legInformation : Bounded 1 LegInformation
  deriving DecidableEq, Repr

namespace ComplexStrategyDirectoryMessage

def encode (message : ComplexStrategyDirectoryMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (StrategyType.encode message.strategyType
    ++ (encodeUInt 1 message.source
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legInformation.val.length)
    ++ (encodeMany LegInformation.encode message.legInformation.val))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (strategyType, bytes) ← StrategyType.decode bytes
  let (source, bytes) ← decodeUInt 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (legInformation_, bytes) ← decodeMany LegInformation.decode numberOfLegs.toNat bytes
  if fits_legInformation : legInformation_.length < 256 ^ 1 then
    pure ({ timestamp, strategyId, strategyType, source, underlyingSymbol, legInformation := ⟨legInformation_, fits_legInformation⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexStrategyDirectoryMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexStrategyDirectoryMessage) : (encode message).length ≤ 7166 := by
  have bound_legInformation := message.legInformation.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, StrategyType.encode_length, Alpha.encode_length, encodeMany_length_const LegInformation.encode 28 LegInformation.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexStrategyDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StrategyType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegInformation.encode LegInformation.decode LegInformation.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legInformation.length_lt]
  rfl

end ComplexStrategyDirectoryMessage

/-- Strategy Open Closed Message: 11 bytes -/
structure StrategyOpenClosedMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  openState : OpenState
  deriving DecidableEq, Repr

namespace StrategyOpenClosedMessage

def encode (message : StrategyOpenClosedMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (OpenState.encode message.openState))

def decode (bytes : List UInt8) : Option (StrategyOpenClosedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (openState, bytes) ← OpenState.decode bytes
  pure ({ timestamp, strategyId, openState }, bytes)

@[simp] theorem encode_length (message : StrategyOpenClosedMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OpenState.encode_length]

theorem encode_length_pos (message : StrategyOpenClosedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyOpenClosedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OpenState.decode_encode, some_bind]
  rfl

end StrategyOpenClosedMessage

/-- Strategy Trading Action Message: 11 bytes -/
structure StrategyTradingActionMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace StrategyTradingActionMessage

def encode (message : StrategyTradingActionMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (CurrentTradingState.encode message.currentTradingState))

def decode (bytes : List UInt8) : Option (StrategyTradingActionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ timestamp, strategyId, currentTradingState }, bytes)

@[simp] theorem encode_length (message : StrategyTradingActionMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : StrategyTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CurrentTradingState.decode_encode, some_bind]
  rfl

end StrategyTradingActionMessage

/-- Strategy Best Bid And Ask Update: 67 bytes -/
structure StrategyBestBidAndAskUpdate where
  timestamp : BitVec 48
  strategyId : BitVec 32
  quoteCondition : QuoteCondition
  bidPrice : BitVec 32
  bidSize : BitVec 32
  bidCustSize : BitVec 32
  bidProCustSize : BitVec 32
  bidNttSize : BitVec 32
  bidMarketSize : BitVec 32
  bidNttMarketSize : BitVec 32
  askPrice : BitVec 32
  askSize : BitVec 32
  askCustSize : BitVec 32
  askProCustSize : BitVec 32
  askNttSize : BitVec 32
  askMarketSize : BitVec 32
  askNttMarketSize : BitVec 32
  deriving DecidableEq, Repr

namespace StrategyBestBidAndAskUpdate

def encode (message : StrategyBestBidAndAskUpdate) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 4 message.bidPrice
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 4 message.bidCustSize
    ++ (encodeUInt 4 message.bidProCustSize
    ++ (encodeUInt 4 message.bidNttSize
    ++ (encodeUInt 4 message.bidMarketSize
    ++ (encodeUInt 4 message.bidNttMarketSize
    ++ (encodeUInt 4 message.askPrice
    ++ (encodeUInt 4 message.askSize
    ++ (encodeUInt 4 message.askCustSize
    ++ (encodeUInt 4 message.askProCustSize
    ++ (encodeUInt 4 message.askNttSize
    ++ (encodeUInt 4 message.askMarketSize
    ++ (encodeUInt 4 message.askNttMarketSize))))))))))))))))

def decode (bytes : List UInt8) : Option (StrategyBestBidAndAskUpdate × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (bidPrice, bytes) ← decodeUInt 4 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (bidCustSize, bytes) ← decodeUInt 4 bytes
  let (bidProCustSize, bytes) ← decodeUInt 4 bytes
  let (bidNttSize, bytes) ← decodeUInt 4 bytes
  let (bidMarketSize, bytes) ← decodeUInt 4 bytes
  let (bidNttMarketSize, bytes) ← decodeUInt 4 bytes
  let (askPrice, bytes) ← decodeUInt 4 bytes
  let (askSize, bytes) ← decodeUInt 4 bytes
  let (askCustSize, bytes) ← decodeUInt 4 bytes
  let (askProCustSize, bytes) ← decodeUInt 4 bytes
  let (askNttSize, bytes) ← decodeUInt 4 bytes
  let (askMarketSize, bytes) ← decodeUInt 4 bytes
  let (askNttMarketSize, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, strategyId, quoteCondition, bidPrice, bidSize, bidCustSize, bidProCustSize, bidNttSize, bidMarketSize, bidNttMarketSize, askPrice, askSize, askCustSize, askProCustSize, askNttSize, askMarketSize, askNttMarketSize }, bytes)

@[simp] theorem encode_length (message : StrategyBestBidAndAskUpdate) : (encode message).length = 67 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : StrategyBestBidAndAskUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyBestBidAndAskUpdate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
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

end StrategyBestBidAndAskUpdate

/-- Strategy Best Bid Update: 39 bytes -/
structure StrategyBestBidUpdate where
  timestamp : BitVec 48
  strategyId : BitVec 32
  quoteCondition : QuoteCondition
  price : BitVec 32
  size : BitVec 32
  custSize : BitVec 32
  proCustSize : BitVec 32
  nttSize : BitVec 32
  marketSize : BitVec 32
  nttMarketSize : BitVec 32
  deriving DecidableEq, Repr

namespace StrategyBestBidUpdate

def encode (message : StrategyBestBidUpdate) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.size
    ++ (encodeUInt 4 message.custSize
    ++ (encodeUInt 4 message.proCustSize
    ++ (encodeUInt 4 message.nttSize
    ++ (encodeUInt 4 message.marketSize
    ++ (encodeUInt 4 message.nttMarketSize)))))))))

def decode (bytes : List UInt8) : Option (StrategyBestBidUpdate × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (size, bytes) ← decodeUInt 4 bytes
  let (custSize, bytes) ← decodeUInt 4 bytes
  let (proCustSize, bytes) ← decodeUInt 4 bytes
  let (nttSize, bytes) ← decodeUInt 4 bytes
  let (marketSize, bytes) ← decodeUInt 4 bytes
  let (nttMarketSize, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, strategyId, quoteCondition, price, size, custSize, proCustSize, nttSize, marketSize, nttMarketSize }, bytes)

@[simp] theorem encode_length (message : StrategyBestBidUpdate) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : StrategyBestBidUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyBestBidUpdate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
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

end StrategyBestBidUpdate

/-- Strategy Best Ask Update: 39 bytes -/
structure StrategyBestAskUpdate where
  timestamp : BitVec 48
  strategyId : BitVec 32
  quoteCondition : QuoteCondition
  price : BitVec 32
  size : BitVec 32
  custSize : BitVec 32
  proCustSize : BitVec 32
  nttSize : BitVec 32
  marketSize : BitVec 32
  nttMarketSize : BitVec 32
  deriving DecidableEq, Repr

namespace StrategyBestAskUpdate

def encode (message : StrategyBestAskUpdate) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.size
    ++ (encodeUInt 4 message.custSize
    ++ (encodeUInt 4 message.proCustSize
    ++ (encodeUInt 4 message.nttSize
    ++ (encodeUInt 4 message.marketSize
    ++ (encodeUInt 4 message.nttMarketSize)))))))))

def decode (bytes : List UInt8) : Option (StrategyBestAskUpdate × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (size, bytes) ← decodeUInt 4 bytes
  let (custSize, bytes) ← decodeUInt 4 bytes
  let (proCustSize, bytes) ← decodeUInt 4 bytes
  let (nttSize, bytes) ← decodeUInt 4 bytes
  let (marketSize, bytes) ← decodeUInt 4 bytes
  let (nttMarketSize, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, strategyId, quoteCondition, price, size, custSize, proCustSize, nttSize, marketSize, nttMarketSize }, bytes)

@[simp] theorem encode_length (message : StrategyBestAskUpdate) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : StrategyBestAskUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyBestAskUpdate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
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

end StrategyBestAskUpdate

/-- Complex Strategy Ticker Message: 51 bytes -/
structure ComplexStrategyTickerMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  lastPrice : BitVec 64
  size : BitVec 32
  volume : BitVec 32
  high : BitVec 64
  low : BitVec 64
  first : BitVec 64
  tradeCondition : Alpha 1
  deriving DecidableEq, Repr

namespace ComplexStrategyTickerMessage

def encode (message : ComplexStrategyTickerMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 4 message.size
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 8 message.high
    ++ (encodeUInt 8 message.low
    ++ (encodeUInt 8 message.first
    ++ (Alpha.encode message.tradeCondition))))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyTickerMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (size, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (high, bytes) ← decodeUInt 8 bytes
  let (low, bytes) ← decodeUInt 8 bytes
  let (first, bytes) ← decodeUInt 8 bytes
  let (tradeCondition, bytes) ← Alpha.decode 1 bytes
  pure ({ timestamp, strategyId, lastPrice, size, volume, high, low, first, tradeCondition }, bytes)

@[simp] theorem encode_length (message : ComplexStrategyTickerMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ComplexStrategyTickerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexStrategyTickerMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexStrategyTickerMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | complexStrategyDirectoryMessage (message : ComplexStrategyDirectoryMessage) -- "R" 0x52
  | strategyOpenClosedMessage (message : StrategyOpenClosedMessage) -- "O" 0x4F
  | strategyTradingActionMessage (message : StrategyTradingActionMessage) -- "H" 0x48
  | strategyBestBidAndAskUpdate (message : StrategyBestBidAndAskUpdate) -- "C" 0x43
  | strategyBestBidUpdate (message : StrategyBestBidUpdate) -- "D" 0x44
  | strategyBestAskUpdate (message : StrategyBestAskUpdate) -- "E" 0x45
  | complexStrategyTickerMessage (message : ComplexStrategyTickerMessage) -- "t" 0x74
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .complexStrategyDirectoryMessage _ => 82
  | .strategyOpenClosedMessage _ => 79
  | .strategyTradingActionMessage _ => 72
  | .strategyBestBidAndAskUpdate _ => 67
  | .strategyBestBidUpdate _ => 68
  | .strategyBestAskUpdate _ => 69
  | .complexStrategyTickerMessage _ => 116

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .complexStrategyDirectoryMessage message => ComplexStrategyDirectoryMessage.encode message
  | .strategyOpenClosedMessage message => StrategyOpenClosedMessage.encode message
  | .strategyTradingActionMessage message => StrategyTradingActionMessage.encode message
  | .strategyBestBidAndAskUpdate message => StrategyBestBidAndAskUpdate.encode message
  | .strategyBestBidUpdate message => StrategyBestBidUpdate.encode message
  | .strategyBestAskUpdate message => StrategyBestAskUpdate.encode message
  | .complexStrategyTickerMessage message => ComplexStrategyTickerMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 7166 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | complexStrategyDirectoryMessage inner =>
    have bound_inner := ComplexStrategyDirectoryMessage.encode_length_le inner
    simp only [encode]
    omega
  | strategyOpenClosedMessage inner =>
    simp only [encode, StrategyOpenClosedMessage.encode_length]
    omega
  | strategyTradingActionMessage inner =>
    simp only [encode, StrategyTradingActionMessage.encode_length]
    omega
  | strategyBestBidAndAskUpdate inner =>
    simp only [encode, StrategyBestBidAndAskUpdate.encode_length]
    omega
  | strategyBestBidUpdate inner =>
    simp only [encode, StrategyBestBidUpdate.encode_length]
    omega
  | strategyBestAskUpdate inner =>
    simp only [encode, StrategyBestAskUpdate.encode_length]
    omega
  | complexStrategyTickerMessage inner =>
    simp only [encode, ComplexStrategyTickerMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (ComplexStrategyDirectoryMessage.decode bytes).map fun (message, rest) => (.complexStrategyDirectoryMessage message, rest)
  else if tag = 79 then (StrategyOpenClosedMessage.decode bytes).map fun (message, rest) => (.strategyOpenClosedMessage message, rest)
  else if tag = 72 then (StrategyTradingActionMessage.decode bytes).map fun (message, rest) => (.strategyTradingActionMessage message, rest)
  else if tag = 67 then (StrategyBestBidAndAskUpdate.decode bytes).map fun (message, rest) => (.strategyBestBidAndAskUpdate message, rest)
  else if tag = 68 then (StrategyBestBidUpdate.decode bytes).map fun (message, rest) => (.strategyBestBidUpdate message, rest)
  else if tag = 69 then (StrategyBestAskUpdate.decode bytes).map fun (message, rest) => (.strategyBestAskUpdate message, rest)
  else if tag = 116 then (ComplexStrategyTickerMessage.decode bytes).map fun (message, rest) => (.complexStrategyTickerMessage message, rest)
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
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | complexStrategyDirectoryMessage inner =>
    have bound_inner := ComplexStrategyDirectoryMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUInt_length]
    omega
  | strategyOpenClosedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StrategyOpenClosedMessage.encode_length]
    omega
  | strategyTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StrategyTradingActionMessage.encode_length]
    omega
  | strategyBestBidAndAskUpdate inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StrategyBestBidAndAskUpdate.encode_length]
    omega
  | strategyBestBidUpdate inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StrategyBestBidUpdate.encode_length]
    omega
  | strategyBestAskUpdate inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StrategyBestAskUpdate.encode_length]
    omega
  | complexStrategyTickerMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ComplexStrategyTickerMessage.encode_length]
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

end Omi.NasdaqIseoptionsTopcomboquotefeedItchV10
