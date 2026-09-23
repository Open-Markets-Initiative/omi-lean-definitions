import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Top Of Market v3.3

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqPhlxoptionsTopofmarketItchV33

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

/-- Option Closing Type: one byte code -/
def OptionClosingType.codes : List UInt8 :=
  [0x4E, 0x4C, 0x57]

inductive OptionClosingType where
  | normal -- Normal
  | late -- Late
  | wcoEarlyClosing -- Wco Early Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionClosingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionClosingType

def toByte : OptionClosingType → UInt8
  | .normal => 0x4E
  | .late => 0x4C
  | .wcoEarlyClosing => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionClosingType :=
  if byte = 0x4E then .normal
  else if byte = 0x4C then .late
  else .wcoEarlyClosing

def ofByte (byte : UInt8) : OptionClosingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionClosingType) : ofByte value.toByte = value := by
  cases value with
  | normal => decide
  | late => decide
  | wcoEarlyClosing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionClosingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionClosingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionClosingType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionClosingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionClosingType

/-- Tradable: one byte code -/
def Tradable.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Tradable where
  | tradable -- Tradable
  | notTradable -- Not Tradable
  | unlisted (byte : { byte : UInt8 // byte ∉ Tradable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tradable

def toByte : Tradable → UInt8
  | .tradable => 0x59
  | .notTradable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tradable :=
  if byte = 0x59 then .tradable
  else .notTradable

def ofByte (byte : UInt8) : Tradable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tradable) : ofByte value.toByte = value := by
  cases value with
  | tradable => decide
  | notTradable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Tradable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Tradable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Tradable) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Tradable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Tradable

/-- Mpv: one byte code -/
def Mpv.codes : List UInt8 :=
  [0x45, 0x53, 0x50]

inductive Mpv where
  | pennyEverywhere -- Penny Everywhere
  | scaled -- Scaled
  | pennyPilot -- Penny Pilot
  | unlisted (byte : { byte : UInt8 // byte ∉ Mpv.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Mpv

def toByte : Mpv → UInt8
  | .pennyEverywhere => 0x45
  | .scaled => 0x53
  | .pennyPilot => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Mpv :=
  if byte = 0x45 then .pennyEverywhere
  else if byte = 0x53 then .scaled
  else .pennyPilot

def ofByte (byte : UInt8) : Mpv :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Mpv) : ofByte value.toByte = value := by
  cases value with
  | pennyEverywhere => decide
  | scaled => decide
  | pennyPilot => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Mpv) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Mpv × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Mpv) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Mpv) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Mpv

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

/-- Open State: one byte code -/
def OpenState.codes : List UInt8 :=
  [0x59, 0x4E]

inductive OpenState where
  | openForAutoExecution -- Open For Auto Execution
  | closedForAutoExecution -- Closed For Auto Execution
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenState

def toByte : OpenState → UInt8
  | .openForAutoExecution => 0x59
  | .closedForAutoExecution => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenState :=
  if byte = 0x59 then .openForAutoExecution
  else .closedForAutoExecution

def ofByte (byte : UInt8) : OpenState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenState) : ofByte value.toByte = value := by
  cases value with
  | openForAutoExecution => decide
  | closedForAutoExecution => decide
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

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x20, 0x46, 0x52, 0x58, 0x59]

inductive QuoteCondition where
  | regularQuoteautoxEligible -- Regular Quoteautox Eligible
  | nonFirmQuote -- Non Firm Quote
  | rotationalQuote -- Rotational Quote
  | bidSideFirm -- Bid Side Firm
  | askSideFirm -- Ask Side Firm
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .regularQuoteautoxEligible => 0x20
  | .nonFirmQuote => 0x46
  | .rotationalQuote => 0x52
  | .bidSideFirm => 0x58
  | .askSideFirm => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x20 then .regularQuoteautoxEligible
  else if byte = 0x46 then .nonFirmQuote
  else if byte = 0x52 then .rotationalQuote
  else if byte = 0x58 then .bidSideFirm
  else .askSideFirm

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | regularQuoteautoxEligible => decide
  | nonFirmQuote => decide
  | rotationalQuote => decide
  | bidSideFirm => decide
  | askSideFirm => decide
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

/-- Timestamp Message: 4 bytes -/
structure TimestampMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace TimestampMessage

def encode (message : TimestampMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (TimestampMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : TimestampMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : TimestampMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimestampMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TimestampMessage

/-- System Event Message: 7 bytes -/
structure SystemEventMessage where
  nanoseconds : BitVec 32
  eventCode : EventCode
  version : BitVec 8
  subversion : BitVec 8
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 1 message.version
    ++ (encodeUInt 1 message.subversion)))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (subversion, bytes) ← decodeUInt 1 bytes
  pure ({ nanoseconds, eventCode, version, subversion }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 7 := by
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Options Directory Message: 39 bytes -/
structure OptionsDirectoryMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  securitySymbol : Alpha 6
  expirationYear : BitVec 8
  expirationMonth : BitVec 8
  expirationDay : BitVec 8
  strikePrice : BitVec 32
  optionType : OptionType
  source : BitVec 8
  underlyingSymbol : Alpha 13
  optionClosingType : OptionClosingType
  tradable : Tradable
  mpv : Mpv
  deriving DecidableEq, Repr

namespace OptionsDirectoryMessage

def encode (message : OptionsDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 1 message.expirationYear
    ++ (encodeUInt 1 message.expirationMonth
    ++ (encodeUInt 1 message.expirationDay
    ++ (encodeUInt 4 message.strikePrice
    ++ (OptionType.encode message.optionType
    ++ (encodeUInt 1 message.source
    ++ (Alpha.encode message.underlyingSymbol
    ++ (OptionClosingType.encode message.optionClosingType
    ++ (Tradable.encode message.tradable
    ++ (Mpv.encode message.mpv))))))))))))

def decode (bytes : List UInt8) : Option (OptionsDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 6 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  let (expirationMonth, bytes) ← decodeUInt 1 bytes
  let (expirationDay, bytes) ← decodeUInt 1 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (source, bytes) ← decodeUInt 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (optionClosingType, bytes) ← OptionClosingType.decode bytes
  let (tradable_, bytes) ← Tradable.decode bytes
  let (mpv, bytes) ← Mpv.decode bytes
  pure ({ nanoseconds, optionId, securitySymbol, expirationYear, expirationMonth, expirationDay, strikePrice, optionType, source, underlyingSymbol, optionClosingType, tradable := tradable_, mpv }, bytes)

@[simp] theorem encode_length (message : OptionsDirectoryMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, OptionClosingType.encode_length, Tradable.encode_length, Mpv.encode_length]

theorem encode_length_pos (message : OptionsDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionClosingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tradable.decode_encode, some_bind]
  dsimp only
  rw [Mpv.decode_encode, some_bind]
  rfl

end OptionsDirectoryMessage

/-- Trading Action Message: 9 bytes -/
structure TradingActionMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace TradingActionMessage

def encode (message : TradingActionMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (CurrentTradingState.encode message.currentTradingState))

def decode (bytes : List UInt8) : Option (TradingActionMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ nanoseconds, optionId, currentTradingState }, bytes)

@[simp] theorem encode_length (message : TradingActionMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : TradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CurrentTradingState.decode_encode, some_bind]
  rfl

end TradingActionMessage

/-- Security Open Closed Message: 9 bytes -/
structure SecurityOpenClosedMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  openState : OpenState
  deriving DecidableEq, Repr

namespace SecurityOpenClosedMessage

def encode (message : SecurityOpenClosedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (OpenState.encode message.openState))

def decode (bytes : List UInt8) : Option (SecurityOpenClosedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (openState, bytes) ← OpenState.decode bytes
  pure ({ nanoseconds, optionId, openState }, bytes)

@[simp] theorem encode_length (message : SecurityOpenClosedMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OpenState.encode_length]

theorem encode_length_pos (message : SecurityOpenClosedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityOpenClosedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OpenState.decode_encode, some_bind]
  rfl

end SecurityOpenClosedMessage

/-- Short Best Bid And Ask Update Message: 17 bytes -/
structure ShortBestBidAndAskUpdateMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  quoteCondition : QuoteCondition
  bidPrice2 : BitVec 16
  bidSize2 : BitVec 16
  askPrice2 : BitVec 16
  askSize2 : BitVec 16
  deriving DecidableEq, Repr

namespace ShortBestBidAndAskUpdateMessage

def encode (message : ShortBestBidAndAskUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 2 message.bidPrice2
    ++ (encodeUInt 2 message.bidSize2
    ++ (encodeUInt 2 message.askPrice2
    ++ (encodeUInt 2 message.askSize2))))))

def decode (bytes : List UInt8) : Option (ShortBestBidAndAskUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (bidPrice2, bytes) ← decodeUInt 2 bytes
  let (bidSize2, bytes) ← decodeUInt 2 bytes
  let (askPrice2, bytes) ← decodeUInt 2 bytes
  let (askSize2, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, optionId, quoteCondition, bidPrice2, bidSize2, askPrice2, askSize2 }, bytes)

@[simp] theorem encode_length (message : ShortBestBidAndAskUpdateMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : ShortBestBidAndAskUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortBestBidAndAskUpdateMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ShortBestBidAndAskUpdateMessage

/-- Long Best Bid And Ask Update Message: 25 bytes -/
structure LongBestBidAndAskUpdateMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  quoteCondition : QuoteCondition
  bidPrice4 : BitVec 32
  bidSize4 : BitVec 32
  askPrice4 : BitVec 32
  askSize4 : BitVec 32
  deriving DecidableEq, Repr

namespace LongBestBidAndAskUpdateMessage

def encode (message : LongBestBidAndAskUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 4 message.bidPrice4
    ++ (encodeUInt 4 message.bidSize4
    ++ (encodeUInt 4 message.askPrice4
    ++ (encodeUInt 4 message.askSize4))))))

def decode (bytes : List UInt8) : Option (LongBestBidAndAskUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (bidPrice4, bytes) ← decodeUInt 4 bytes
  let (bidSize4, bytes) ← decodeUInt 4 bytes
  let (askPrice4, bytes) ← decodeUInt 4 bytes
  let (askSize4, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, optionId, quoteCondition, bidPrice4, bidSize4, askPrice4, askSize4 }, bytes)

@[simp] theorem encode_length (message : LongBestBidAndAskUpdateMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : LongBestBidAndAskUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongBestBidAndAskUpdateMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LongBestBidAndAskUpdateMessage

/-- Short Best Ask Update Message: 13 bytes -/
structure ShortBestAskUpdateMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  quoteCondition : QuoteCondition
  price2 : BitVec 16
  size2 : BitVec 16
  deriving DecidableEq, Repr

namespace ShortBestAskUpdateMessage

def encode (message : ShortBestAskUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 2 message.price2
    ++ (encodeUInt 2 message.size2))))

def decode (bytes : List UInt8) : Option (ShortBestAskUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (price2, bytes) ← decodeUInt 2 bytes
  let (size2, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, optionId, quoteCondition, price2, size2 }, bytes)

@[simp] theorem encode_length (message : ShortBestAskUpdateMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : ShortBestAskUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortBestAskUpdateMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ShortBestAskUpdateMessage

/-- Short Best Bid Update Message: 13 bytes -/
structure ShortBestBidUpdateMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  quoteCondition : QuoteCondition
  price2 : BitVec 16
  size2 : BitVec 16
  deriving DecidableEq, Repr

namespace ShortBestBidUpdateMessage

def encode (message : ShortBestBidUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 2 message.price2
    ++ (encodeUInt 2 message.size2))))

def decode (bytes : List UInt8) : Option (ShortBestBidUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (price2, bytes) ← decodeUInt 2 bytes
  let (size2, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, optionId, quoteCondition, price2, size2 }, bytes)

@[simp] theorem encode_length (message : ShortBestBidUpdateMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : ShortBestBidUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortBestBidUpdateMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ShortBestBidUpdateMessage

/-- Long Best Ask Update Message: 17 bytes -/
structure LongBestAskUpdateMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  quoteCondition : QuoteCondition
  price4 : BitVec 32
  size4 : BitVec 32
  deriving DecidableEq, Repr

namespace LongBestAskUpdateMessage

def encode (message : LongBestAskUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 4 message.price4
    ++ (encodeUInt 4 message.size4))))

def decode (bytes : List UInt8) : Option (LongBestAskUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (price4, bytes) ← decodeUInt 4 bytes
  let (size4, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, optionId, quoteCondition, price4, size4 }, bytes)

@[simp] theorem encode_length (message : LongBestAskUpdateMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : LongBestAskUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongBestAskUpdateMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LongBestAskUpdateMessage

/-- Long Best Bid Update Message: 17 bytes -/
structure LongBestBidUpdateMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  quoteCondition : QuoteCondition
  price4 : BitVec 32
  size4 : BitVec 32
  deriving DecidableEq, Repr

namespace LongBestBidUpdateMessage

def encode (message : LongBestBidUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 4 message.price4
    ++ (encodeUInt 4 message.size4))))

def decode (bytes : List UInt8) : Option (LongBestBidUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (price4, bytes) ← decodeUInt 4 bytes
  let (size4, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, optionId, quoteCondition, price4, size4 }, bytes)

@[simp] theorem encode_length (message : LongBestBidUpdateMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : LongBestBidUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongBestBidUpdateMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LongBestBidUpdateMessage

/-- Trade Report Message: 21 bytes -/
structure TradeReportMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  crossId : BitVec 32
  tradeCondition : Alpha 1
  price4 : BitVec 32
  volume : BitVec 32
  deriving DecidableEq, Repr

namespace TradeReportMessage

def encode (message : TradeReportMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.crossId
    ++ (Alpha.encode message.tradeCondition
    ++ (encodeUInt 4 message.price4
    ++ (encodeUInt 4 message.volume)))))

def decode (bytes : List UInt8) : Option (TradeReportMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (tradeCondition, bytes) ← Alpha.decode 1 bytes
  let (price4, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, optionId, crossId, tradeCondition, price4, volume }, bytes)

@[simp] theorem encode_length (message : TradeReportMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeReportMessage

/-- Broken Trade Report Message: 20 bytes -/
structure BrokenTradeReportMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  originalCrossId : BitVec 32
  originalPrice : BitVec 32
  originalVolume : BitVec 32
  deriving DecidableEq, Repr

namespace BrokenTradeReportMessage

def encode (message : BrokenTradeReportMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.originalCrossId
    ++ (encodeUInt 4 message.originalPrice
    ++ (encodeUInt 4 message.originalVolume))))

def decode (bytes : List UInt8) : Option (BrokenTradeReportMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (originalCrossId, bytes) ← decodeUInt 4 bytes
  let (originalPrice, bytes) ← decodeUInt 4 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, optionId, originalCrossId, originalPrice, originalVolume }, bytes)

@[simp] theorem encode_length (message : BrokenTradeReportMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BrokenTradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeReportMessage) (rest : List UInt8) :
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

end BrokenTradeReportMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | timestampMessage (message : TimestampMessage) -- "T" 0x54
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | optionsDirectoryMessage (message : OptionsDirectoryMessage) -- "D" 0x44
  | tradingActionMessage (message : TradingActionMessage) -- "H" 0x48
  | securityOpenClosedMessage (message : SecurityOpenClosedMessage) -- "O" 0x4F
  | shortBestBidAndAskUpdateMessage (message : ShortBestBidAndAskUpdateMessage) -- "q" 0x71
  | longBestBidAndAskUpdateMessage (message : LongBestBidAndAskUpdateMessage) -- "Q" 0x51
  | shortBestAskUpdateMessage (message : ShortBestAskUpdateMessage) -- "a" 0x61
  | shortBestBidUpdateMessage (message : ShortBestBidUpdateMessage) -- "b" 0x62
  | longBestAskUpdateMessage (message : LongBestAskUpdateMessage) -- "A" 0x41
  | longBestBidUpdateMessage (message : LongBestBidUpdateMessage) -- "B" 0x42
  | tradeReportMessage (message : TradeReportMessage) -- "R" 0x52
  | brokenTradeReportMessage (message : BrokenTradeReportMessage) -- "X" 0x58
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .timestampMessage _ => 84
  | .systemEventMessage _ => 83
  | .optionsDirectoryMessage _ => 68
  | .tradingActionMessage _ => 72
  | .securityOpenClosedMessage _ => 79
  | .shortBestBidAndAskUpdateMessage _ => 113
  | .longBestBidAndAskUpdateMessage _ => 81
  | .shortBestAskUpdateMessage _ => 97
  | .shortBestBidUpdateMessage _ => 98
  | .longBestAskUpdateMessage _ => 65
  | .longBestBidUpdateMessage _ => 66
  | .tradeReportMessage _ => 82
  | .brokenTradeReportMessage _ => 88

def encode : Payload → List UInt8
  | .timestampMessage message => TimestampMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .optionsDirectoryMessage message => OptionsDirectoryMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .securityOpenClosedMessage message => SecurityOpenClosedMessage.encode message
  | .shortBestBidAndAskUpdateMessage message => ShortBestBidAndAskUpdateMessage.encode message
  | .longBestBidAndAskUpdateMessage message => LongBestBidAndAskUpdateMessage.encode message
  | .shortBestAskUpdateMessage message => ShortBestAskUpdateMessage.encode message
  | .shortBestBidUpdateMessage message => ShortBestBidUpdateMessage.encode message
  | .longBestAskUpdateMessage message => LongBestAskUpdateMessage.encode message
  | .longBestBidUpdateMessage message => LongBestBidUpdateMessage.encode message
  | .tradeReportMessage message => TradeReportMessage.encode message
  | .brokenTradeReportMessage message => BrokenTradeReportMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 39 := by
  cases message with
  | timestampMessage inner =>
    simp only [encode, TimestampMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | optionsDirectoryMessage inner =>
    simp only [encode, OptionsDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [encode, TradingActionMessage.encode_length]
    omega
  | securityOpenClosedMessage inner =>
    simp only [encode, SecurityOpenClosedMessage.encode_length]
    omega
  | shortBestBidAndAskUpdateMessage inner =>
    simp only [encode, ShortBestBidAndAskUpdateMessage.encode_length]
    omega
  | longBestBidAndAskUpdateMessage inner =>
    simp only [encode, LongBestBidAndAskUpdateMessage.encode_length]
    omega
  | shortBestAskUpdateMessage inner =>
    simp only [encode, ShortBestAskUpdateMessage.encode_length]
    omega
  | shortBestBidUpdateMessage inner =>
    simp only [encode, ShortBestBidUpdateMessage.encode_length]
    omega
  | longBestAskUpdateMessage inner =>
    simp only [encode, LongBestAskUpdateMessage.encode_length]
    omega
  | longBestBidUpdateMessage inner =>
    simp only [encode, LongBestBidUpdateMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [encode, TradeReportMessage.encode_length]
    omega
  | brokenTradeReportMessage inner =>
    simp only [encode, BrokenTradeReportMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (TimestampMessage.decode bytes).map fun (message, rest) => (.timestampMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 68 then (OptionsDirectoryMessage.decode bytes).map fun (message, rest) => (.optionsDirectoryMessage message, rest)
  else if tag = 72 then (TradingActionMessage.decode bytes).map fun (message, rest) => (.tradingActionMessage message, rest)
  else if tag = 79 then (SecurityOpenClosedMessage.decode bytes).map fun (message, rest) => (.securityOpenClosedMessage message, rest)
  else if tag = 113 then (ShortBestBidAndAskUpdateMessage.decode bytes).map fun (message, rest) => (.shortBestBidAndAskUpdateMessage message, rest)
  else if tag = 81 then (LongBestBidAndAskUpdateMessage.decode bytes).map fun (message, rest) => (.longBestBidAndAskUpdateMessage message, rest)
  else if tag = 97 then (ShortBestAskUpdateMessage.decode bytes).map fun (message, rest) => (.shortBestAskUpdateMessage message, rest)
  else if tag = 98 then (ShortBestBidUpdateMessage.decode bytes).map fun (message, rest) => (.shortBestBidUpdateMessage message, rest)
  else if tag = 65 then (LongBestAskUpdateMessage.decode bytes).map fun (message, rest) => (.longBestAskUpdateMessage message, rest)
  else if tag = 66 then (LongBestBidUpdateMessage.decode bytes).map fun (message, rest) => (.longBestBidUpdateMessage message, rest)
  else if tag = 82 then (TradeReportMessage.decode bytes).map fun (message, rest) => (.tradeReportMessage message, rest)
  else if tag = 88 then (BrokenTradeReportMessage.decode bytes).map fun (message, rest) => (.brokenTradeReportMessage message, rest)
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
  | timestampMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TimestampMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | optionsDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OptionsDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingActionMessage.encode_length]
    omega
  | securityOpenClosedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityOpenClosedMessage.encode_length]
    omega
  | shortBestBidAndAskUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ShortBestBidAndAskUpdateMessage.encode_length]
    omega
  | longBestBidAndAskUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LongBestBidAndAskUpdateMessage.encode_length]
    omega
  | shortBestAskUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ShortBestAskUpdateMessage.encode_length]
    omega
  | shortBestBidUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ShortBestBidUpdateMessage.encode_length]
    omega
  | longBestAskUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LongBestAskUpdateMessage.encode_length]
    omega
  | longBestBidUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LongBestBidUpdateMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeReportMessage.encode_length]
    omega
  | brokenTradeReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BrokenTradeReportMessage.encode_length]
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

end Omi.NasdaqPhlxoptionsTopofmarketItchV33
