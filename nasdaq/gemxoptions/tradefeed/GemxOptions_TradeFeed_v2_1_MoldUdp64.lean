import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Trade Feed v2.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqGemxoptionsTradefeedItchV21MoldUdp64

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
  [0x43, 0x50, 0x4E]

inductive OptionType where
  | call -- Call
  | put -- Put
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .call => 0x43
  | .put => 0x50
  | .notApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .call
  else if byte = 0x50 then .put
  else .notApplicable

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | notApplicable => decide
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

/-- Closing Type: one byte code -/
def ClosingType.codes : List UInt8 :=
  [0x4E, 0x4C, 0x57]

inductive ClosingType where
  | normalHours -- Normal Hours
  | lateHours -- Late Hours
  | wcoEarlyClosing -- Wco Early Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ ClosingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClosingType

def toByte : ClosingType → UInt8
  | .normalHours => 0x4E
  | .lateHours => 0x4C
  | .wcoEarlyClosing => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClosingType :=
  if byte = 0x4E then .normalHours
  else if byte = 0x4C then .lateHours
  else .wcoEarlyClosing

def ofByte (byte : UInt8) : ClosingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClosingType) : ofByte value.toByte = value := by
  cases value with
  | normalHours => decide
  | lateHours => decide
  | wcoEarlyClosing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClosingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClosingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClosingType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ClosingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClosingType

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
  [0x42, 0x53, 0x48, 0x54, 0x49, 0x4F, 0x52, 0x58]

inductive CurrentTradingState where
  | buySideSuspended -- Buy Side Suspended
  | sellSideSuspended -- Sell Side Suspended
  | haltInEffect -- Halt In Effect
  | continuousTrading -- Continuous Trading
  | preOpen -- Pre Open
  | openingAuction -- Opening Auction
  | reOpening -- Re Opening
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .buySideSuspended => 0x42
  | .sellSideSuspended => 0x53
  | .haltInEffect => 0x48
  | .continuousTrading => 0x54
  | .preOpen => 0x49
  | .openingAuction => 0x4F
  | .reOpening => 0x52
  | .closed => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x42 then .buySideSuspended
  else if byte = 0x53 then .sellSideSuspended
  else if byte = 0x48 then .haltInEffect
  else if byte = 0x54 then .continuousTrading
  else if byte = 0x49 then .preOpen
  else if byte = 0x4F then .openingAuction
  else if byte = 0x52 then .reOpening
  else .closed

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | buySideSuspended => decide
  | sellSideSuspended => decide
  | haltInEffect => decide
  | continuousTrading => decide
  | preOpen => decide
  | openingAuction => decide
  | reOpening => decide
  | closed => decide
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

/-- System Event Message: 11 bytes -/
structure SystemEventMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (EventCode.encode message.eventCode))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ trackingNumber, timestamp, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 11 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Derivative Directory Message: 62 bytes -/
structure DerivativeDirectoryMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  securitySymbol : Alpha 8
  expirationYear : BitVec 8
  expirationMonth : BitVec 8
  expirationDay : BitVec 8
  explicitStrikePrice : BitVec 32
  optionType : OptionType
  underlyingSymbol : Alpha 13
  closingType : ClosingType
  tradable : Tradable
  mpv : Mpv
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace DerivativeDirectoryMessage

def encode (message : DerivativeDirectoryMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 1 message.expirationYear
    ++ (encodeUInt 1 message.expirationMonth
    ++ (encodeUInt 1 message.expirationDay
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.underlyingSymbol
    ++ (ClosingType.encode message.closingType
    ++ (Tradable.encode message.tradable
    ++ (Mpv.encode message.mpv
    ++ (Alpha.encode message.reserved16)))))))))))))

def decode (bytes : List UInt8) : Option (DerivativeDirectoryMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 8 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  let (expirationMonth, bytes) ← decodeUInt 1 bytes
  let (expirationDay, bytes) ← decodeUInt 1 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (closingType, bytes) ← ClosingType.decode bytes
  let (tradable_, bytes) ← Tradable.decode bytes
  let (mpv, bytes) ← Mpv.decode bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ trackingNumber, timestamp, instrumentId, securitySymbol, expirationYear, expirationMonth, expirationDay, explicitStrikePrice, optionType, underlyingSymbol, closingType, tradable := tradable_, mpv, reserved16 }, bytes)

@[simp] theorem encode_length (message : DerivativeDirectoryMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, ClosingType.encode_length, Tradable.encode_length, Mpv.encode_length]

theorem encode_length_pos (message : DerivativeDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DerivativeDirectoryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClosingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tradable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Mpv.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DerivativeDirectoryMessage

/-- Trading Action Message: 15 bytes -/
structure TradingActionMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace TradingActionMessage

def encode (message : TradingActionMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (CurrentTradingState.encode message.currentTradingState)))

def decode (bytes : List UInt8) : Option (TradingActionMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ trackingNumber, timestamp, instrumentId, currentTradingState }, bytes)

@[simp] theorem encode_length (message : TradingActionMessage) : (encode message).length = 15 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CurrentTradingState.decode_encode, some_bind]
  rfl

end TradingActionMessage

/-- Trade Message: 43 bytes -/
structure TradeMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  crossId : BitVec 32
  tradeCondition : Alpha 1
  price : BitVec 32
  volume : BitVec 32
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.crossId
    ++ (Alpha.encode message.tradeCondition
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume
    ++ (Alpha.encode message.reserved16)))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (tradeCondition, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ trackingNumber, timestamp, instrumentId, crossId, tradeCondition, price, volume, reserved16 }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Broken Trade Report Message: 26 bytes -/
structure BrokenTradeReportMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  originalCrossId : BitVec 32
  originalPrice : BitVec 32
  originalVolume : BitVec 32
  deriving DecidableEq, Repr

namespace BrokenTradeReportMessage

def encode (message : BrokenTradeReportMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.originalCrossId
    ++ (encodeUInt 4 message.originalPrice
    ++ (encodeUInt 4 message.originalVolume)))))

def decode (bytes : List UInt8) : Option (BrokenTradeReportMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (originalCrossId, bytes) ← decodeUInt 4 bytes
  let (originalPrice, bytes) ← decodeUInt 4 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, originalCrossId, originalPrice, originalVolume }, bytes)

@[simp] theorem encode_length (message : BrokenTradeReportMessage) : (encode message).length = 26 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BrokenTradeReportMessage

/-- Any Udp Payload, selected by Message Type -/
inductive UdpPayload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | derivativeDirectoryMessage (message : DerivativeDirectoryMessage) -- "m" 0x6D
  | tradingActionMessage (message : TradingActionMessage) -- "H" 0x48
  | tradeMessage (message : TradeMessage) -- "R" 0x52
  | brokenTradeReportMessage (message : BrokenTradeReportMessage) -- "X" 0x58
  deriving DecidableEq, Repr

namespace UdpPayload

/-- The Message Type each message is sent under -/
def tag : UdpPayload → BitVec 8
  | .systemEventMessage _ => 83
  | .derivativeDirectoryMessage _ => 109
  | .tradingActionMessage _ => 72
  | .tradeMessage _ => 82
  | .brokenTradeReportMessage _ => 88

def encode : UdpPayload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .derivativeDirectoryMessage message => DerivativeDirectoryMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .brokenTradeReportMessage message => BrokenTradeReportMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UdpPayload) : (encode message).length ≤ 62 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | derivativeDirectoryMessage inner =>
    simp only [encode, DerivativeDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [encode, TradingActionMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | brokenTradeReportMessage inner =>
    simp only [encode, BrokenTradeReportMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UdpPayload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 109 then (DerivativeDirectoryMessage.decode bytes).map fun (message, rest) => (.derivativeDirectoryMessage message, rest)
  else if tag = 72 then (TradingActionMessage.decode bytes).map fun (message, rest) => (.tradingActionMessage message, rest)
  else if tag = 82 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 88 then (BrokenTradeReportMessage.decode bytes).map fun (message, rest) => (.brokenTradeReportMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UdpPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UdpPayload

/-- Message -/
structure Message where
  udpPayload : UdpPayload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (UdpPayload.tag message.udpPayload)
    ++ (UdpPayload.encode message.udpPayload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (udpPayload, bytes) ← UdpPayload.decode messageType bytes
  pure ({ udpPayload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UdpPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.udpPayload with
  | systemEventMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | derivativeDirectoryMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, DerivativeDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, TradingActionMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | brokenTradeReportMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, BrokenTradeReportMessage.encode_length]
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

/-- Mold Udp 64 Packet -/
structure MoldUdp64Packet where
  udpSession : Alpha 10
  udpSequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace MoldUdp64Packet

def encode (message : MoldUdp64Packet) : List UInt8 :=
  Alpha.encode message.udpSession
    ++ (encodeUInt 8 message.udpSequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (MoldUdp64Packet × List UInt8) := do
  let (udpSession, bytes) ← Alpha.decode 10 bytes
  let (udpSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ udpSession, udpSequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : MoldUdp64Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : MoldUdp64Packet) (rest : List UInt8) :
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

end MoldUdp64Packet

end Omi.NasdaqGemxoptionsTradefeedItchV21MoldUdp64
