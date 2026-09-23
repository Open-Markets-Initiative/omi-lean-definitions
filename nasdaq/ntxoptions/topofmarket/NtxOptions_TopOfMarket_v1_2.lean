import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Top Of Market v1.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNtxoptionsTopofmarketItchV12

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4D, 0x45, 0x43]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfMarketHours -- Start Of Market Hours
  | endOfMarketHours -- End Of Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfMarketHours => 0x51
  | .endOfMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x45 then .endOfSystemHours
  else .endOfMessages

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfMarketHours => decide
  | endOfMarketHours => decide
  | endOfSystemHours => decide
  | endOfMessages => decide
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

/-- Tradable: one byte code -/
def Tradable.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Tradable where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ Tradable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tradable

def toByte : Tradable → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tradable :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : Tradable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tradable) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
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

/-- Minimum Price Variation: one byte code -/
def MinimumPriceVariation.codes : List UInt8 :=
  [0x45, 0x53, 0x50]

inductive MinimumPriceVariation where
  | pennyEverywhere -- Penny Everywhere
  | scaled -- Scaled
  | pennyPilot -- Penny Pilot
  | unlisted (byte : { byte : UInt8 // byte ∉ MinimumPriceVariation.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MinimumPriceVariation

def toByte : MinimumPriceVariation → UInt8
  | .pennyEverywhere => 0x45
  | .scaled => 0x53
  | .pennyPilot => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MinimumPriceVariation :=
  if byte = 0x45 then .pennyEverywhere
  else if byte = 0x53 then .scaled
  else .pennyPilot

def ofByte (byte : UInt8) : MinimumPriceVariation :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MinimumPriceVariation) : ofByte value.toByte = value := by
  cases value with
  | pennyEverywhere => decide
  | scaled => decide
  | pennyPilot => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MinimumPriceVariation) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MinimumPriceVariation × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MinimumPriceVariation) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MinimumPriceVariation) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MinimumPriceVariation

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x48, 0x54]

inductive CurrentTradingState where
  | halt -- Halt
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .halt => 0x48
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .halt
  else .trading

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | halt => decide
  | trading => decide
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

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x46, 0x52, 0x58, 0x59, 0x20]

inductive QuoteCondition where
  | nonfirmQuote -- Nonfirm Quote
  | rotationalQuote -- Rotational Quote
  | bidSideFirm -- Bid Side Firm
  | askSideFirm -- Ask Side Firm
  | regularQuote -- Regular Quote
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .nonfirmQuote => 0x46
  | .rotationalQuote => 0x52
  | .bidSideFirm => 0x58
  | .askSideFirm => 0x59
  | .regularQuote => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x46 then .nonfirmQuote
  else if byte = 0x52 then .rotationalQuote
  else if byte = 0x58 then .bidSideFirm
  else if byte = 0x59 then .askSideFirm
  else .regularQuote

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | nonfirmQuote => decide
  | rotationalQuote => decide
  | bidSideFirm => decide
  | askSideFirm => decide
  | regularQuote => decide
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
  optionClosingType : Alpha 1
  tradable : Tradable
  minimumPriceVariation : MinimumPriceVariation
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
    ++ (Alpha.encode message.optionClosingType
    ++ (Tradable.encode message.tradable
    ++ (MinimumPriceVariation.encode message.minimumPriceVariation))))))))))))

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
  let (optionClosingType, bytes) ← Alpha.decode 1 bytes
  let (tradable, bytes) ← Tradable.decode bytes
  let (minimumPriceVariation, bytes) ← MinimumPriceVariation.decode bytes
  pure ({ nanoseconds, optionId, securitySymbol, expirationYear, expirationMonth, expirationDay, strikePrice, optionType, source, underlyingSymbol, optionClosingType, tradable, minimumPriceVariation }, bytes)

@[simp] theorem encode_length (message : OptionsDirectoryMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, Tradable.encode_length, MinimumPriceVariation.encode_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tradable.decode_encode, some_bind]
  dsimp only
  rw [MinimumPriceVariation.decode_encode, some_bind]
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

/-- Security Open Message: 9 bytes -/
structure SecurityOpenMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  openState : OpenState
  deriving DecidableEq, Repr

namespace SecurityOpenMessage

def encode (message : SecurityOpenMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (OpenState.encode message.openState))

def decode (bytes : List UInt8) : Option (SecurityOpenMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (openState, bytes) ← OpenState.decode bytes
  pure ({ nanoseconds, optionId, openState }, bytes)

@[simp] theorem encode_length (message : SecurityOpenMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OpenState.encode_length]

theorem encode_length_pos (message : SecurityOpenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityOpenMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OpenState.decode_encode, some_bind]
  rfl

end SecurityOpenMessage

/-- Best Bid And Ask Update Short Form Message: 17 bytes -/
structure BestBidAndAskUpdateShortFormMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  quoteCondition : QuoteCondition
  bidPrice : BitVec 16
  bidSize : BitVec 16
  askPrice : BitVec 16
  askSize : BitVec 16
  deriving DecidableEq, Repr

namespace BestBidAndAskUpdateShortFormMessage

def encode (message : BestBidAndAskUpdateShortFormMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 2 message.bidPrice
    ++ (encodeUInt 2 message.bidSize
    ++ (encodeUInt 2 message.askPrice
    ++ (encodeUInt 2 message.askSize))))))

def decode (bytes : List UInt8) : Option (BestBidAndAskUpdateShortFormMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (bidPrice, bytes) ← decodeUInt 2 bytes
  let (bidSize, bytes) ← decodeUInt 2 bytes
  let (askPrice, bytes) ← decodeUInt 2 bytes
  let (askSize, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, optionId, quoteCondition, bidPrice, bidSize, askPrice, askSize }, bytes)

@[simp] theorem encode_length (message : BestBidAndAskUpdateShortFormMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : BestBidAndAskUpdateShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestBidAndAskUpdateShortFormMessage) (rest : List UInt8) :
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

end BestBidAndAskUpdateShortFormMessage

/-- Best Bid And Ask Update Long Form Message: 25 bytes -/
structure BestBidAndAskUpdateLongFormMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  quoteCondition : QuoteCondition
  bidPriceLong : BitVec 32
  bidSizeLong : BitVec 32
  askPriceLong : BitVec 32
  askSizeLong : BitVec 32
  deriving DecidableEq, Repr

namespace BestBidAndAskUpdateLongFormMessage

def encode (message : BestBidAndAskUpdateLongFormMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 4 message.bidPriceLong
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 4 message.askPriceLong
    ++ (encodeUInt 4 message.askSizeLong))))))

def decode (bytes : List UInt8) : Option (BestBidAndAskUpdateLongFormMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (bidPriceLong, bytes) ← decodeUInt 4 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (askPriceLong, bytes) ← decodeUInt 4 bytes
  let (askSizeLong, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, optionId, quoteCondition, bidPriceLong, bidSizeLong, askPriceLong, askSizeLong }, bytes)

@[simp] theorem encode_length (message : BestBidAndAskUpdateLongFormMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : BestBidAndAskUpdateLongFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestBidAndAskUpdateLongFormMessage) (rest : List UInt8) :
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

end BestBidAndAskUpdateLongFormMessage

/-- Best Bid Update Short Form Message: 13 bytes -/
structure BestBidUpdateShortFormMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  quoteCondition : QuoteCondition
  price : BitVec 16
  size : BitVec 16
  deriving DecidableEq, Repr

namespace BestBidUpdateShortFormMessage

def encode (message : BestBidUpdateShortFormMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 2 message.price
    ++ (encodeUInt 2 message.size))))

def decode (bytes : List UInt8) : Option (BestBidUpdateShortFormMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (price, bytes) ← decodeUInt 2 bytes
  let (size, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, optionId, quoteCondition, price, size }, bytes)

@[simp] theorem encode_length (message : BestBidUpdateShortFormMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : BestBidUpdateShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestBidUpdateShortFormMessage) (rest : List UInt8) :
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

end BestBidUpdateShortFormMessage

/-- Best Ask Update Short Form Message: 13 bytes -/
structure BestAskUpdateShortFormMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  quoteCondition : QuoteCondition
  price : BitVec 16
  size : BitVec 16
  deriving DecidableEq, Repr

namespace BestAskUpdateShortFormMessage

def encode (message : BestAskUpdateShortFormMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 2 message.price
    ++ (encodeUInt 2 message.size))))

def decode (bytes : List UInt8) : Option (BestAskUpdateShortFormMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (price, bytes) ← decodeUInt 2 bytes
  let (size, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, optionId, quoteCondition, price, size }, bytes)

@[simp] theorem encode_length (message : BestAskUpdateShortFormMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : BestAskUpdateShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestAskUpdateShortFormMessage) (rest : List UInt8) :
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

end BestAskUpdateShortFormMessage

/-- Best Bid Update Long Form Message: 17 bytes -/
structure BestBidUpdateLongFormMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  quoteCondition : QuoteCondition
  priceLong : BitVec 32
  sizeLong : BitVec 32
  deriving DecidableEq, Repr

namespace BestBidUpdateLongFormMessage

def encode (message : BestBidUpdateLongFormMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.sizeLong))))

def decode (bytes : List UInt8) : Option (BestBidUpdateLongFormMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (sizeLong, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, optionId, quoteCondition, priceLong, sizeLong }, bytes)

@[simp] theorem encode_length (message : BestBidUpdateLongFormMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : BestBidUpdateLongFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestBidUpdateLongFormMessage) (rest : List UInt8) :
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

end BestBidUpdateLongFormMessage

/-- Best Ask Update Long Form Message: 17 bytes -/
structure BestAskUpdateLongFormMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  quoteCondition : QuoteCondition
  priceLong : BitVec 32
  sizeLong : BitVec 32
  deriving DecidableEq, Repr

namespace BestAskUpdateLongFormMessage

def encode (message : BestAskUpdateLongFormMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.sizeLong))))

def decode (bytes : List UInt8) : Option (BestAskUpdateLongFormMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (sizeLong, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, optionId, quoteCondition, priceLong, sizeLong }, bytes)

@[simp] theorem encode_length (message : BestAskUpdateLongFormMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : BestAskUpdateLongFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestAskUpdateLongFormMessage) (rest : List UInt8) :
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

end BestAskUpdateLongFormMessage

/-- Trade Report Message: 21 bytes -/
structure TradeReportMessage where
  nanoseconds : BitVec 32
  optionId : BitVec 32
  crossId : BitVec 32
  tradeCondition : Alpha 1
  priceLong : BitVec 32
  volume : BitVec 32
  deriving DecidableEq, Repr

namespace TradeReportMessage

def encode (message : TradeReportMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.optionId
    ++ (encodeUInt 4 message.crossId
    ++ (Alpha.encode message.tradeCondition
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volume)))))

def decode (bytes : List UInt8) : Option (TradeReportMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (tradeCondition, bytes) ← Alpha.decode 1 bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, optionId, crossId, tradeCondition, priceLong, volume }, bytes)

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
  | securityOpenMessage (message : SecurityOpenMessage) -- "O" 0x4F
  | bestBidAndAskUpdateShortFormMessage (message : BestBidAndAskUpdateShortFormMessage) -- "q" 0x71
  | bestBidAndAskUpdateLongFormMessage (message : BestBidAndAskUpdateLongFormMessage) -- "Q" 0x51
  | bestBidUpdateShortFormMessage (message : BestBidUpdateShortFormMessage) -- "b" 0x62
  | bestAskUpdateShortFormMessage (message : BestAskUpdateShortFormMessage) -- "a" 0x61
  | bestBidUpdateLongFormMessage (message : BestBidUpdateLongFormMessage) -- "B" 0x42
  | bestAskUpdateLongFormMessage (message : BestAskUpdateLongFormMessage) -- "A" 0x41
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
  | .securityOpenMessage _ => 79
  | .bestBidAndAskUpdateShortFormMessage _ => 113
  | .bestBidAndAskUpdateLongFormMessage _ => 81
  | .bestBidUpdateShortFormMessage _ => 98
  | .bestAskUpdateShortFormMessage _ => 97
  | .bestBidUpdateLongFormMessage _ => 66
  | .bestAskUpdateLongFormMessage _ => 65
  | .tradeReportMessage _ => 82
  | .brokenTradeReportMessage _ => 88

def encode : Payload → List UInt8
  | .timestampMessage message => TimestampMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .optionsDirectoryMessage message => OptionsDirectoryMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .securityOpenMessage message => SecurityOpenMessage.encode message
  | .bestBidAndAskUpdateShortFormMessage message => BestBidAndAskUpdateShortFormMessage.encode message
  | .bestBidAndAskUpdateLongFormMessage message => BestBidAndAskUpdateLongFormMessage.encode message
  | .bestBidUpdateShortFormMessage message => BestBidUpdateShortFormMessage.encode message
  | .bestAskUpdateShortFormMessage message => BestAskUpdateShortFormMessage.encode message
  | .bestBidUpdateLongFormMessage message => BestBidUpdateLongFormMessage.encode message
  | .bestAskUpdateLongFormMessage message => BestAskUpdateLongFormMessage.encode message
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
  | securityOpenMessage inner =>
    simp only [encode, SecurityOpenMessage.encode_length]
    omega
  | bestBidAndAskUpdateShortFormMessage inner =>
    simp only [encode, BestBidAndAskUpdateShortFormMessage.encode_length]
    omega
  | bestBidAndAskUpdateLongFormMessage inner =>
    simp only [encode, BestBidAndAskUpdateLongFormMessage.encode_length]
    omega
  | bestBidUpdateShortFormMessage inner =>
    simp only [encode, BestBidUpdateShortFormMessage.encode_length]
    omega
  | bestAskUpdateShortFormMessage inner =>
    simp only [encode, BestAskUpdateShortFormMessage.encode_length]
    omega
  | bestBidUpdateLongFormMessage inner =>
    simp only [encode, BestBidUpdateLongFormMessage.encode_length]
    omega
  | bestAskUpdateLongFormMessage inner =>
    simp only [encode, BestAskUpdateLongFormMessage.encode_length]
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
  else if tag = 79 then (SecurityOpenMessage.decode bytes).map fun (message, rest) => (.securityOpenMessage message, rest)
  else if tag = 113 then (BestBidAndAskUpdateShortFormMessage.decode bytes).map fun (message, rest) => (.bestBidAndAskUpdateShortFormMessage message, rest)
  else if tag = 81 then (BestBidAndAskUpdateLongFormMessage.decode bytes).map fun (message, rest) => (.bestBidAndAskUpdateLongFormMessage message, rest)
  else if tag = 98 then (BestBidUpdateShortFormMessage.decode bytes).map fun (message, rest) => (.bestBidUpdateShortFormMessage message, rest)
  else if tag = 97 then (BestAskUpdateShortFormMessage.decode bytes).map fun (message, rest) => (.bestAskUpdateShortFormMessage message, rest)
  else if tag = 66 then (BestBidUpdateLongFormMessage.decode bytes).map fun (message, rest) => (.bestBidUpdateLongFormMessage message, rest)
  else if tag = 65 then (BestAskUpdateLongFormMessage.decode bytes).map fun (message, rest) => (.bestAskUpdateLongFormMessage message, rest)
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
  | securityOpenMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityOpenMessage.encode_length]
    omega
  | bestBidAndAskUpdateShortFormMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BestBidAndAskUpdateShortFormMessage.encode_length]
    omega
  | bestBidAndAskUpdateLongFormMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BestBidAndAskUpdateLongFormMessage.encode_length]
    omega
  | bestBidUpdateShortFormMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BestBidUpdateShortFormMessage.encode_length]
    omega
  | bestAskUpdateShortFormMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BestAskUpdateShortFormMessage.encode_length]
    omega
  | bestBidUpdateLongFormMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BestBidUpdateLongFormMessage.encode_length]
    omega
  | bestAskUpdateLongFormMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BestAskUpdateLongFormMessage.encode_length]
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

end Omi.NasdaqNtxoptionsTopofmarketItchV12
