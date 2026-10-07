import Wire

/-!
# London Stock Exchange MiFID II Post Trade Replay v24.4

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Allowed Book Types is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Tcp Unit's Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LsegTradeechoMifid2posttradereplayGtpV244

/-- Login Status: one byte code -/
def LoginStatus.codes : List UInt8 :=
  [0x41, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66]

inductive LoginStatus where
  | loginAccepted -- Login Accepted
  | compIdInactiveSuspended -- Comp Id Inactive Suspended
  | loginLimitReached -- Login Limit Reached
  | serviceUnavailable -- Service Unavailable
  | maximumConnectionsLimitReached -- Maximum Connections Limit Reached
  | failedOther -- Failed Other
  | invalidCompIdOrIpAddress -- Invalid Comp Id Or Ip Address
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginStatus

def toByte : LoginStatus → UInt8
  | .loginAccepted => 0x41
  | .compIdInactiveSuspended => 0x61
  | .loginLimitReached => 0x62
  | .serviceUnavailable => 0x63
  | .maximumConnectionsLimitReached => 0x64
  | .failedOther => 0x65
  | .invalidCompIdOrIpAddress => 0x66
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginStatus :=
  if byte = 0x41 then .loginAccepted
  else if byte = 0x61 then .compIdInactiveSuspended
  else if byte = 0x62 then .loginLimitReached
  else if byte = 0x63 then .serviceUnavailable
  else if byte = 0x64 then .maximumConnectionsLimitReached
  else if byte = 0x65 then .failedOther
  else .invalidCompIdOrIpAddress

def ofByte (byte : UInt8) : LoginStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginStatus) : ofByte value.toByte = value := by
  cases value with
  | loginAccepted => decide
  | compIdInactiveSuspended => decide
  | loginLimitReached => decide
  | serviceUnavailable => decide
  | maximumConnectionsLimitReached => decide
  | failedOther => decide
  | invalidCompIdOrIpAddress => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LoginStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LoginStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LoginStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LoginStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LoginStatus

/-- Replay Status: one byte code -/
def ReplayStatus.codes : List UInt8 :=
  [0x41, 0x44, 0x4F, 0x55, 0x63, 0x65]

inductive ReplayStatus where
  | requestAccepted -- Request Accepted
  | requestLimitReached -- Request Limit Reached
  | outOfRange -- Out Of Range
  | replayUnavailable -- Replay Unavailable
  | concurrentLimitReached -- Concurrent Limit Reached
  | failedOther -- Failed Other
  | unlisted (byte : { byte : UInt8 // byte ∉ ReplayStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReplayStatus

def toByte : ReplayStatus → UInt8
  | .requestAccepted => 0x41
  | .requestLimitReached => 0x44
  | .outOfRange => 0x4F
  | .replayUnavailable => 0x55
  | .concurrentLimitReached => 0x63
  | .failedOther => 0x65
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReplayStatus :=
  if byte = 0x41 then .requestAccepted
  else if byte = 0x44 then .requestLimitReached
  else if byte = 0x4F then .outOfRange
  else if byte = 0x55 then .replayUnavailable
  else if byte = 0x63 then .concurrentLimitReached
  else .failedOther

def ofByte (byte : UInt8) : ReplayStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReplayStatus) : ofByte value.toByte = value := by
  cases value with
  | requestAccepted => decide
  | requestLimitReached => decide
  | outOfRange => decide
  | replayUnavailable => decide
  | concurrentLimitReached => decide
  | failedOther => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReplayStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReplayStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReplayStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReplayStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReplayStatus

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x50]

inductive TradingStatus where
  | inactiveOrUnderlyingSuspended -- Inactive Or Underlying Suspended
  | suspended -- Suspended
  | active -- Active
  | regulatoryHalt -- Regulatory Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .inactiveOrUnderlyingSuspended => 0x31
  | .suspended => 0x32
  | .active => 0x33
  | .regulatoryHalt => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x31 then .inactiveOrUnderlyingSuspended
  else if byte = 0x32 then .suspended
  else if byte = 0x33 then .active
  else .regulatoryHalt

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | inactiveOrUnderlyingSuspended => decide
  | suspended => decide
  | active => decide
  | regulatoryHalt => decide
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

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x54, 0x50]

inductive EventCode where
  | startOfOpen -- Start Of Open
  | startOfPreClose -- Start Of Pre Close
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfOpen => 0x54
  | .startOfPreClose => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x54 then .startOfOpen
  else .startOfPreClose

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfOpen => decide
  | startOfPreClose => decide
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

/-- Transaction To Be Cleared: one byte code -/
def TransactionToBeCleared.codes : List UInt8 :=
  [0x30, 0x31]

inductive TransactionToBeCleared where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionToBeCleared.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionToBeCleared

def toByte : TransactionToBeCleared → UInt8
  | .no => 0x30
  | .yes => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionToBeCleared :=
  if byte = 0x30 then .no
  else .yes

def ofByte (byte : UInt8) : TransactionToBeCleared :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionToBeCleared) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionToBeCleared) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionToBeCleared × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionToBeCleared) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TransactionToBeCleared) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionToBeCleared

/-- Market Mechanism: one byte code -/
def MarketMechanism.codes : List UInt8 :=
  [0x34]

inductive MarketMechanism where
  | offBook -- Off Book
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketMechanism.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketMechanism

def toByte : MarketMechanism → UInt8
  | .offBook => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : MarketMechanism :=
  .offBook

def ofByte (byte : UInt8) : MarketMechanism :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketMechanism) : ofByte value.toByte = value := by
  cases value with
  | offBook => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketMechanism) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketMechanism × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketMechanism) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketMechanism) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketMechanism

/-- Trading Mode: one byte code -/
def TradingMode.codes : List UInt8 :=
  [0x35, 0x36, 0x37]

inductive TradingMode where
  | onExchange -- On Exchange
  | offExchange -- Off Exchange
  | systemicInternaliser -- Systemic Internaliser
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingMode

def toByte : TradingMode → UInt8
  | .onExchange => 0x35
  | .offExchange => 0x36
  | .systemicInternaliser => 0x37
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingMode :=
  if byte = 0x35 then .onExchange
  else if byte = 0x36 then .offExchange
  else .systemicInternaliser

def ofByte (byte : UInt8) : TradingMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingMode) : ofByte value.toByte = value := by
  cases value with
  | onExchange => decide
  | offExchange => decide
  | systemicInternaliser => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingMode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingMode

/-- Transaction Category: one byte code -/
def TransactionCategory.codes : List UInt8 :=
  [0x52, 0x5A, 0x59, 0x47, 0x48, 0x2D]

inductive TransactionCategory where
  | tradeThatHasReceivedPriceImprovement -- Trade That Has Received Price Improvement
  | packageTradeExcludingExchangeForPhysicals -- Package Trade Excluding Exchange For Physicals
  | exchangeForPhysicalsTrade -- Exchange For Physicals Trade
  | rfmdGiveUpTrade -- Rfmd Give Up Trade
  | rfmdGiveUpTradeGiveAndExchangeForPhysicalsTrade -- Rfmd Give Up Trade Give And Exchange For Physicals Trade
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionCategory

def toByte : TransactionCategory → UInt8
  | .tradeThatHasReceivedPriceImprovement => 0x52
  | .packageTradeExcludingExchangeForPhysicals => 0x5A
  | .exchangeForPhysicalsTrade => 0x59
  | .rfmdGiveUpTrade => 0x47
  | .rfmdGiveUpTradeGiveAndExchangeForPhysicalsTrade => 0x48
  | .none_ => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionCategory :=
  if byte = 0x52 then .tradeThatHasReceivedPriceImprovement
  else if byte = 0x5A then .packageTradeExcludingExchangeForPhysicals
  else if byte = 0x59 then .exchangeForPhysicalsTrade
  else if byte = 0x47 then .rfmdGiveUpTrade
  else if byte = 0x48 then .rfmdGiveUpTradeGiveAndExchangeForPhysicalsTrade
  else .none_

def ofByte (byte : UInt8) : TransactionCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionCategory) : ofByte value.toByte = value := by
  cases value with
  | tradeThatHasReceivedPriceImprovement => decide
  | packageTradeExcludingExchangeForPhysicals => decide
  | exchangeForPhysicalsTrade => decide
  | rfmdGiveUpTrade => decide
  | rfmdGiveUpTradeGiveAndExchangeForPhysicalsTrade => decide
  | none_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TransactionCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionCategory

/-- Negotiation Indicator: one byte code -/
def NegotiationIndicator.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x37, 0x38, 0x2D]

inductive NegotiationIndicator where
  | negotiatedTradeInLiquidFinancialInstruments -- Negotiated Trade In Liquid Financial Instruments
  | negotiatedTradeInIlliquidFinancialInstruments -- Negotiated Trade In Illiquid Financial Instruments
  | negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPrice -- Negotiated Trade Subject To Conditions Other Than The Current Market Price
  | negotiatedTradeLargerThanLisBroughtOntoAVenue -- Negotiated Trade Larger Than Lis Brought Onto A Venue
  | negotiatedTradeWithPretradeTransparencyWaiver -- Negotiated Trade With Pretrade Transparency Waiver
  | notANegotiatedTrade -- Not A Negotiated Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ NegotiationIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NegotiationIndicator

def toByte : NegotiationIndicator → UInt8
  | .negotiatedTradeInLiquidFinancialInstruments => 0x31
  | .negotiatedTradeInIlliquidFinancialInstruments => 0x32
  | .negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPrice => 0x33
  | .negotiatedTradeLargerThanLisBroughtOntoAVenue => 0x37
  | .negotiatedTradeWithPretradeTransparencyWaiver => 0x38
  | .notANegotiatedTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NegotiationIndicator :=
  if byte = 0x31 then .negotiatedTradeInLiquidFinancialInstruments
  else if byte = 0x32 then .negotiatedTradeInIlliquidFinancialInstruments
  else if byte = 0x33 then .negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPrice
  else if byte = 0x37 then .negotiatedTradeLargerThanLisBroughtOntoAVenue
  else if byte = 0x38 then .negotiatedTradeWithPretradeTransparencyWaiver
  else .notANegotiatedTrade

def ofByte (byte : UInt8) : NegotiationIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NegotiationIndicator) : ofByte value.toByte = value := by
  cases value with
  | negotiatedTradeInLiquidFinancialInstruments => decide
  | negotiatedTradeInIlliquidFinancialInstruments => decide
  | negotiatedTradeSubjectToConditionsOtherThanTheCurrentMarketPrice => decide
  | negotiatedTradeLargerThanLisBroughtOntoAVenue => decide
  | negotiatedTradeWithPretradeTransparencyWaiver => decide
  | notANegotiatedTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NegotiationIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NegotiationIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NegotiationIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NegotiationIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NegotiationIndicator

/-- Agency Cross Indicator: one byte code -/
def AgencyCrossIndicator.codes : List UInt8 :=
  [0x58, 0x2D]

inductive AgencyCrossIndicator where
  | agencyCrossTrade -- Agency Cross Trade
  | noAgencyCrossTrade -- No Agency Cross Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ AgencyCrossIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AgencyCrossIndicator

def toByte : AgencyCrossIndicator → UInt8
  | .agencyCrossTrade => 0x58
  | .noAgencyCrossTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AgencyCrossIndicator :=
  if byte = 0x58 then .agencyCrossTrade
  else .noAgencyCrossTrade

def ofByte (byte : UInt8) : AgencyCrossIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AgencyCrossIndicator) : ofByte value.toByte = value := by
  cases value with
  | agencyCrossTrade => decide
  | noAgencyCrossTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AgencyCrossIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AgencyCrossIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AgencyCrossIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AgencyCrossIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AgencyCrossIndicator

/-- Modification Indicator: one byte code -/
def ModificationIndicator.codes : List UInt8 :=
  [0x43, 0x41, 0x2D]

inductive ModificationIndicator where
  | tradeCancellation -- Trade Cancellation
  | tradeAmendment -- Trade Amendment
  | newTrade -- New Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ ModificationIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ModificationIndicator

def toByte : ModificationIndicator → UInt8
  | .tradeCancellation => 0x43
  | .tradeAmendment => 0x41
  | .newTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ModificationIndicator :=
  if byte = 0x43 then .tradeCancellation
  else if byte = 0x41 then .tradeAmendment
  else .newTrade

def ofByte (byte : UInt8) : ModificationIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ModificationIndicator) : ofByte value.toByte = value := by
  cases value with
  | tradeCancellation => decide
  | tradeAmendment => decide
  | newTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ModificationIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ModificationIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ModificationIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ModificationIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ModificationIndicator

/-- Login Request Message: 8 bytes -/
structure LoginRequestMessage where
  username : Alpha 8
  deriving DecidableEq, Repr

namespace LoginRequestMessage

def encode (message : LoginRequestMessage) : List UInt8 :=
  Alpha.encode message.username

def decode (bytes : List UInt8) : Option (LoginRequestMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 8 bytes
  pure ({ username }, bytes)

@[simp] theorem encode_length (message : LoginRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestMessage

/-- Replay Request Message: 12 bytes -/
structure ReplayRequestMessage where
  firstMessage : BitVec 32
  count : BitVec 32
  requestId : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayRequestMessage

def encode (message : ReplayRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.firstMessage
    ++ (encodeUIntLE 4 message.count
    ++ (encodeUIntLE 4 message.requestId))

def decode (bytes : List UInt8) : Option (ReplayRequestMessage × List UInt8) := do
  let (firstMessage, bytes) ← decodeUIntLE 4 bytes
  let (count, bytes) ← decodeUIntLE 4 bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  pure ({ firstMessage, count, requestId }, bytes)

@[simp] theorem encode_length (message : ReplayRequestMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ReplayRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReplayRequestMessage

/-- Login Response Message: 1 bytes -/
structure LoginResponseMessage where
  loginStatus : LoginStatus
  deriving DecidableEq, Repr

namespace LoginResponseMessage

def encode (message : LoginResponseMessage) : List UInt8 :=
  LoginStatus.encode message.loginStatus

def decode (bytes : List UInt8) : Option (LoginResponseMessage × List UInt8) := do
  let (loginStatus, bytes) ← LoginStatus.decode bytes
  pure ({ loginStatus }, bytes)

@[simp] theorem encode_length (message : LoginResponseMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [LoginStatus.encode_length]

theorem encode_length_pos (message : LoginResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [LoginStatus.decode_encode, some_bind]
  rfl

end LoginResponseMessage

/-- Replay Response Message: 13 bytes -/
structure ReplayResponseMessage where
  firstMessage : BitVec 32
  count : BitVec 32
  replayStatus : ReplayStatus
  requestId : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayResponseMessage

def encode (message : ReplayResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.firstMessage
    ++ (encodeUIntLE 4 message.count
    ++ (ReplayStatus.encode message.replayStatus
    ++ (encodeUIntLE 4 message.requestId)))

def decode (bytes : List UInt8) : Option (ReplayResponseMessage × List UInt8) := do
  let (firstMessage, bytes) ← decodeUIntLE 4 bytes
  let (count, bytes) ← decodeUIntLE 4 bytes
  let (replayStatus, bytes) ← ReplayStatus.decode bytes
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  pure ({ firstMessage, count, replayStatus, requestId }, bytes)

@[simp] theorem encode_length (message : ReplayResponseMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ReplayStatus.encode_length]

theorem encode_length_pos (message : ReplayResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ReplayStatus.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReplayResponseMessage

/-- Replay And Recovery Complete Message: 5 bytes -/
structure ReplayAndRecoveryCompleteMessage where
  requestId : BitVec 32
  tradingStatus : TradingStatus
  deriving DecidableEq, Repr

namespace ReplayAndRecoveryCompleteMessage

def encode (message : ReplayAndRecoveryCompleteMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestId
    ++ (TradingStatus.encode message.tradingStatus)

def decode (bytes : List UInt8) : Option (ReplayAndRecoveryCompleteMessage × List UInt8) := do
  let (requestId, bytes) ← decodeUIntLE 4 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  pure ({ requestId, tradingStatus }, bytes)

@[simp] theorem encode_length (message : ReplayAndRecoveryCompleteMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradingStatus.encode_length]

theorem encode_length_pos (message : ReplayAndRecoveryCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayAndRecoveryCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [TradingStatus.decode_encode, some_bind]
  rfl

end ReplayAndRecoveryCompleteMessage

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
  priceBandTolerances : BitVec 64
  dynamicCircuitBreakerTolerances : BitVec 64
  staticCircuitBreakerTolerances : BitVec 64
  segment : Alpha 6
  reserved12 : Alpha 12
  reserved11 : Alpha 11
  currency : Alpha 3
  reserved1 : Alpha 1
  reserved4 : Alpha 4
  averageDailyTurnover : BitVec 64
  reserved8 : Alpha 8
  secondReserved1 : Alpha 1
  secondReserved8 : Alpha 8
  thirdReserved8 : Alpha 8
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
    ++ (encodeUIntLE 8 message.priceBandTolerances
    ++ (encodeUIntLE 8 message.dynamicCircuitBreakerTolerances
    ++ (encodeUIntLE 8 message.staticCircuitBreakerTolerances
    ++ (Alpha.encode message.segment
    ++ (Alpha.encode message.reserved12
    ++ (Alpha.encode message.reserved11
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 8 message.averageDailyTurnover
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.secondReserved1
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.thirdReserved8))))))))))))))))))))

def decode (bytes : List UInt8) : Option (InstrumentDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (allowedBookTypes, bytes) ← decodeUIntLE 1 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (venueInstrumentId, bytes) ← Alpha.decode 11 bytes
  let (tickId, bytes) ← Alpha.decode 2 bytes
  let (priceBandTolerances, bytes) ← decodeUIntLE 8 bytes
  let (dynamicCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (staticCircuitBreakerTolerances, bytes) ← decodeUIntLE 8 bytes
  let (segment, bytes) ← Alpha.decode 6 bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  let (reserved11, bytes) ← Alpha.decode 11 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (averageDailyTurnover, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (thirdReserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ timestamp, instrument, isin, allowedBookTypes, sourceVenue, venueInstrumentId, tickId, priceBandTolerances, dynamicCircuitBreakerTolerances, staticCircuitBreakerTolerances, segment, reserved12, reserved11, currency, reserved1, reserved4, averageDailyTurnover, reserved8, secondReserved1, secondReserved8, thirdReserved8 }, bytes)

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

/-- Statistics Message: 74 bytes -/
structure StatisticsMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  sourceVenue : BitVec 16
  volume : BitVec 64
  volumeOnbookOnly : BitVec 64
  vwap : BitVec 64
  vwapOnbookOnly : BitVec 64
  numberOfTrades : BitVec 32
  numberOfTradesOnbookOnly : BitVec 32
  turnover : BitVec 64
  turnoverOnbookOnly : BitVec 64
  deriving DecidableEq, Repr

namespace StatisticsMessage

def encode (message : StatisticsMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (encodeUIntLE 8 message.volume
    ++ (encodeUIntLE 8 message.volumeOnbookOnly
    ++ (encodeUIntLE 8 message.vwap
    ++ (encodeUIntLE 8 message.vwapOnbookOnly
    ++ (encodeUIntLE 4 message.numberOfTrades
    ++ (encodeUIntLE 4 message.numberOfTradesOnbookOnly
    ++ (encodeUIntLE 8 message.turnover
    ++ (encodeUIntLE 8 message.turnoverOnbookOnly))))))))))

def decode (bytes : List UInt8) : Option (StatisticsMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (volume, bytes) ← decodeUIntLE 8 bytes
  let (volumeOnbookOnly, bytes) ← decodeUIntLE 8 bytes
  let (vwap, bytes) ← decodeUIntLE 8 bytes
  let (vwapOnbookOnly, bytes) ← decodeUIntLE 8 bytes
  let (numberOfTrades, bytes) ← decodeUIntLE 4 bytes
  let (numberOfTradesOnbookOnly, bytes) ← decodeUIntLE 4 bytes
  let (turnover, bytes) ← decodeUIntLE 8 bytes
  let (turnoverOnbookOnly, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, instrument, sourceVenue, volume, volumeOnbookOnly, vwap, vwapOnbookOnly, numberOfTrades, numberOfTradesOnbookOnly, turnover, turnoverOnbookOnly }, bytes)

@[simp] theorem encode_length (message : StatisticsMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : StatisticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatisticsMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StatisticsMessage

/-- Mifid Ii Trade Report Message: 433 bytes -/
structure MifidIiTradeReportMessage where
  timestamp : BitVec 64
  instrument : BitVec 64
  transactionIdentificationCode : Alpha 52
  totalNumberOfTransactions : BitVec 32
  reserved8 : Alpha 8
  sourceVenue : BitVec 16
  miFidPrice : Alpha 20
  miFidQuantity : Alpha 20
  miFidTradingDateAndTime : Alpha 27
  instrumentIdentificationCodeType : Alpha 4
  instrumentIdentificationCode : Alpha 12
  priceNotation : Alpha 4
  priceCurrency : Alpha 3
  notionalAmount : Alpha 20
  notionalCurrency : Alpha 3
  venueOfExecution : Alpha 4
  publicationDateAndTime : Alpha 27
  benchmarkTransactionFlag : Alpha 4
  agencyCrossTradeFlag : Alpha 4
  nonPriceFormingTransactionsFlag : Alpha 4
  nonPriceContributionToDiscovery : Alpha 4
  specialDividendFlag : Alpha 4
  ptDeferralReasonFlag : Alpha 4
  referencePriceTransactionFlag : Alpha 4
  ntLiquidityFlag : Alpha 4
  ntPriceConditionsFlag : Alpha 4
  algoTransactionFlag : Alpha 4
  ptIlliquidFlag : Alpha 4
  priceImprovementFlag : Alpha 4
  cancellationFlag : Alpha 4
  amendmentFlag : Alpha 4
  duplicateFlag : Alpha 4
  exchangeForPhysicalsFlag : Alpha 4
  limitedDetailsFlag : Alpha 4
  ldFullDetailsFlag : Alpha 4
  dailyAggregatedTransactionFlag : Alpha 4
  daFullDetailsFlag : Alpha 4
  volumeOmissionFlag : Alpha 4
  voFullDetailsFlag : Alpha 4
  fourWeeksAggregationFlag : Alpha 4
  faFullDetailsFlag : Alpha 4
  indefiniteAggregationFlag : Alpha 4
  volumeOmissionForSovereignDebtFlag : Alpha 4
  consecutiveAggregationFlag : Alpha 4
  reserved1 : Alpha 1
  venueType : BitVec 8
  venueBookDefinitionId : BitVec 8
  venueMeasurementUnitNotation : Alpha 25
  quantityInMeasurementUnit : Alpha 20
  transactionToBeCleared : TransactionToBeCleared
  emissionAllowanceType : Alpha 4
  venueOfPublication : Alpha 4
  marketMechanism : MarketMechanism
  tradingMode : TradingMode
  transactionCategory : TransactionCategory
  negotiationIndicator : NegotiationIndicator
  agencyCrossIndicator : AgencyCrossIndicator
  modificationIndicator : ModificationIndicator
  referencePriceIndicator : Alpha 1
  specialDividendIndicator : Alpha 1
  offBookAutomatedIndicator : Alpha 1
  priceFormationIndicator : Alpha 1
  algorithmicIndicator : Alpha 1
  postTradeDeferralReason : Alpha 1
  deferralEnrichmentType : Alpha 1
  duplicativeIndicator : Alpha 1
  thirdcountryTradingVenueOfExecution : Alpha 4
  portfolioTransactionFlag : Alpha 4
  contingentTransactionFlag : Alpha 4
  priceConditions : Alpha 4
  marketClosingPriceFlag : Alpha 4
  ntLargeInScaleFlag : Alpha 4
  ntPreTradeTransparencyFlag : Alpha 4
  deriving DecidableEq, Repr

namespace MifidIiTradeReportMessage

def encode (message : MifidIiTradeReportMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.instrument
    ++ (Alpha.encode message.transactionIdentificationCode
    ++ (encodeUIntLE 4 message.totalNumberOfTransactions
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 2 message.sourceVenue
    ++ (Alpha.encode message.miFidPrice
    ++ (Alpha.encode message.miFidQuantity
    ++ (Alpha.encode message.miFidTradingDateAndTime
    ++ (Alpha.encode message.instrumentIdentificationCodeType
    ++ (Alpha.encode message.instrumentIdentificationCode
    ++ (Alpha.encode message.priceNotation
    ++ (Alpha.encode message.priceCurrency
    ++ (Alpha.encode message.notionalAmount
    ++ (Alpha.encode message.notionalCurrency
    ++ (Alpha.encode message.venueOfExecution
    ++ (Alpha.encode message.publicationDateAndTime
    ++ (Alpha.encode message.benchmarkTransactionFlag
    ++ (Alpha.encode message.agencyCrossTradeFlag
    ++ (Alpha.encode message.nonPriceFormingTransactionsFlag
    ++ (Alpha.encode message.nonPriceContributionToDiscovery
    ++ (Alpha.encode message.specialDividendFlag
    ++ (Alpha.encode message.ptDeferralReasonFlag
    ++ (Alpha.encode message.referencePriceTransactionFlag
    ++ (Alpha.encode message.ntLiquidityFlag
    ++ (Alpha.encode message.ntPriceConditionsFlag
    ++ (Alpha.encode message.algoTransactionFlag
    ++ (Alpha.encode message.ptIlliquidFlag
    ++ (Alpha.encode message.priceImprovementFlag
    ++ (Alpha.encode message.cancellationFlag
    ++ (Alpha.encode message.amendmentFlag
    ++ (Alpha.encode message.duplicateFlag
    ++ (Alpha.encode message.exchangeForPhysicalsFlag
    ++ (Alpha.encode message.limitedDetailsFlag
    ++ (Alpha.encode message.ldFullDetailsFlag
    ++ (Alpha.encode message.dailyAggregatedTransactionFlag
    ++ (Alpha.encode message.daFullDetailsFlag
    ++ (Alpha.encode message.volumeOmissionFlag
    ++ (Alpha.encode message.voFullDetailsFlag
    ++ (Alpha.encode message.fourWeeksAggregationFlag
    ++ (Alpha.encode message.faFullDetailsFlag
    ++ (Alpha.encode message.indefiniteAggregationFlag
    ++ (Alpha.encode message.volumeOmissionForSovereignDebtFlag
    ++ (Alpha.encode message.consecutiveAggregationFlag
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 1 message.venueType
    ++ (encodeUIntLE 1 message.venueBookDefinitionId
    ++ (Alpha.encode message.venueMeasurementUnitNotation
    ++ (Alpha.encode message.quantityInMeasurementUnit
    ++ (TransactionToBeCleared.encode message.transactionToBeCleared
    ++ (Alpha.encode message.emissionAllowanceType
    ++ (Alpha.encode message.venueOfPublication
    ++ (MarketMechanism.encode message.marketMechanism
    ++ (TradingMode.encode message.tradingMode
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (NegotiationIndicator.encode message.negotiationIndicator
    ++ (AgencyCrossIndicator.encode message.agencyCrossIndicator
    ++ (ModificationIndicator.encode message.modificationIndicator
    ++ (Alpha.encode message.referencePriceIndicator
    ++ (Alpha.encode message.specialDividendIndicator
    ++ (Alpha.encode message.offBookAutomatedIndicator
    ++ (Alpha.encode message.priceFormationIndicator
    ++ (Alpha.encode message.algorithmicIndicator
    ++ (Alpha.encode message.postTradeDeferralReason
    ++ (Alpha.encode message.deferralEnrichmentType
    ++ (Alpha.encode message.duplicativeIndicator
    ++ (Alpha.encode message.thirdcountryTradingVenueOfExecution
    ++ (Alpha.encode message.portfolioTransactionFlag
    ++ (Alpha.encode message.contingentTransactionFlag
    ++ (Alpha.encode message.priceConditions
    ++ (Alpha.encode message.marketClosingPriceFlag
    ++ (Alpha.encode message.ntLargeInScaleFlag
    ++ (Alpha.encode message.ntPreTradeTransparencyFlag))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MifidIiTradeReportMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← decodeUIntLE 8 bytes
  let (transactionIdentificationCode, bytes) ← Alpha.decode 52 bytes
  let (totalNumberOfTransactions, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (sourceVenue, bytes) ← decodeUIntLE 2 bytes
  let (miFidPrice, bytes) ← Alpha.decode 20 bytes
  let (miFidQuantity, bytes) ← Alpha.decode 20 bytes
  let (miFidTradingDateAndTime, bytes) ← Alpha.decode 27 bytes
  let (instrumentIdentificationCodeType, bytes) ← Alpha.decode 4 bytes
  let (instrumentIdentificationCode, bytes) ← Alpha.decode 12 bytes
  let (priceNotation, bytes) ← Alpha.decode 4 bytes
  let (priceCurrency, bytes) ← Alpha.decode 3 bytes
  let (notionalAmount, bytes) ← Alpha.decode 20 bytes
  let (notionalCurrency, bytes) ← Alpha.decode 3 bytes
  let (venueOfExecution, bytes) ← Alpha.decode 4 bytes
  let (publicationDateAndTime, bytes) ← Alpha.decode 27 bytes
  let (benchmarkTransactionFlag, bytes) ← Alpha.decode 4 bytes
  let (agencyCrossTradeFlag, bytes) ← Alpha.decode 4 bytes
  let (nonPriceFormingTransactionsFlag, bytes) ← Alpha.decode 4 bytes
  let (nonPriceContributionToDiscovery, bytes) ← Alpha.decode 4 bytes
  let (specialDividendFlag, bytes) ← Alpha.decode 4 bytes
  let (ptDeferralReasonFlag, bytes) ← Alpha.decode 4 bytes
  let (referencePriceTransactionFlag, bytes) ← Alpha.decode 4 bytes
  let (ntLiquidityFlag, bytes) ← Alpha.decode 4 bytes
  let (ntPriceConditionsFlag, bytes) ← Alpha.decode 4 bytes
  let (algoTransactionFlag, bytes) ← Alpha.decode 4 bytes
  let (ptIlliquidFlag, bytes) ← Alpha.decode 4 bytes
  let (priceImprovementFlag, bytes) ← Alpha.decode 4 bytes
  let (cancellationFlag, bytes) ← Alpha.decode 4 bytes
  let (amendmentFlag, bytes) ← Alpha.decode 4 bytes
  let (duplicateFlag, bytes) ← Alpha.decode 4 bytes
  let (exchangeForPhysicalsFlag, bytes) ← Alpha.decode 4 bytes
  let (limitedDetailsFlag, bytes) ← Alpha.decode 4 bytes
  let (ldFullDetailsFlag, bytes) ← Alpha.decode 4 bytes
  let (dailyAggregatedTransactionFlag, bytes) ← Alpha.decode 4 bytes
  let (daFullDetailsFlag, bytes) ← Alpha.decode 4 bytes
  let (volumeOmissionFlag, bytes) ← Alpha.decode 4 bytes
  let (voFullDetailsFlag, bytes) ← Alpha.decode 4 bytes
  let (fourWeeksAggregationFlag, bytes) ← Alpha.decode 4 bytes
  let (faFullDetailsFlag, bytes) ← Alpha.decode 4 bytes
  let (indefiniteAggregationFlag, bytes) ← Alpha.decode 4 bytes
  let (volumeOmissionForSovereignDebtFlag, bytes) ← Alpha.decode 4 bytes
  let (consecutiveAggregationFlag, bytes) ← Alpha.decode 4 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (venueType, bytes) ← decodeUIntLE 1 bytes
  let (venueBookDefinitionId, bytes) ← decodeUIntLE 1 bytes
  let (venueMeasurementUnitNotation, bytes) ← Alpha.decode 25 bytes
  let (quantityInMeasurementUnit, bytes) ← Alpha.decode 20 bytes
  let (transactionToBeCleared, bytes) ← TransactionToBeCleared.decode bytes
  let (emissionAllowanceType, bytes) ← Alpha.decode 4 bytes
  let (venueOfPublication, bytes) ← Alpha.decode 4 bytes
  let (marketMechanism, bytes) ← MarketMechanism.decode bytes
  let (tradingMode, bytes) ← TradingMode.decode bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (negotiationIndicator, bytes) ← NegotiationIndicator.decode bytes
  let (agencyCrossIndicator, bytes) ← AgencyCrossIndicator.decode bytes
  let (modificationIndicator, bytes) ← ModificationIndicator.decode bytes
  let (referencePriceIndicator, bytes) ← Alpha.decode 1 bytes
  let (specialDividendIndicator, bytes) ← Alpha.decode 1 bytes
  let (offBookAutomatedIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceFormationIndicator, bytes) ← Alpha.decode 1 bytes
  let (algorithmicIndicator, bytes) ← Alpha.decode 1 bytes
  let (postTradeDeferralReason, bytes) ← Alpha.decode 1 bytes
  let (deferralEnrichmentType, bytes) ← Alpha.decode 1 bytes
  let (duplicativeIndicator, bytes) ← Alpha.decode 1 bytes
  let (thirdcountryTradingVenueOfExecution, bytes) ← Alpha.decode 4 bytes
  let (portfolioTransactionFlag, bytes) ← Alpha.decode 4 bytes
  let (contingentTransactionFlag, bytes) ← Alpha.decode 4 bytes
  let (priceConditions, bytes) ← Alpha.decode 4 bytes
  let (marketClosingPriceFlag, bytes) ← Alpha.decode 4 bytes
  let (ntLargeInScaleFlag, bytes) ← Alpha.decode 4 bytes
  let (ntPreTradeTransparencyFlag, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, instrument, transactionIdentificationCode, totalNumberOfTransactions, reserved8, sourceVenue, miFidPrice, miFidQuantity, miFidTradingDateAndTime, instrumentIdentificationCodeType, instrumentIdentificationCode, priceNotation, priceCurrency, notionalAmount, notionalCurrency, venueOfExecution, publicationDateAndTime, benchmarkTransactionFlag, agencyCrossTradeFlag, nonPriceFormingTransactionsFlag, nonPriceContributionToDiscovery, specialDividendFlag, ptDeferralReasonFlag, referencePriceTransactionFlag, ntLiquidityFlag, ntPriceConditionsFlag, algoTransactionFlag, ptIlliquidFlag, priceImprovementFlag, cancellationFlag, amendmentFlag, duplicateFlag, exchangeForPhysicalsFlag, limitedDetailsFlag, ldFullDetailsFlag, dailyAggregatedTransactionFlag, daFullDetailsFlag, volumeOmissionFlag, voFullDetailsFlag, fourWeeksAggregationFlag, faFullDetailsFlag, indefiniteAggregationFlag, volumeOmissionForSovereignDebtFlag, consecutiveAggregationFlag, reserved1, venueType, venueBookDefinitionId, venueMeasurementUnitNotation, quantityInMeasurementUnit, transactionToBeCleared, emissionAllowanceType, venueOfPublication, marketMechanism, tradingMode, transactionCategory, negotiationIndicator, agencyCrossIndicator, modificationIndicator, referencePriceIndicator, specialDividendIndicator, offBookAutomatedIndicator, priceFormationIndicator, algorithmicIndicator, postTradeDeferralReason, deferralEnrichmentType, duplicativeIndicator, thirdcountryTradingVenueOfExecution, portfolioTransactionFlag, contingentTransactionFlag, priceConditions, marketClosingPriceFlag, ntLargeInScaleFlag, ntPreTradeTransparencyFlag }, bytes)

@[simp] theorem encode_length (message : MifidIiTradeReportMessage) : (encode message).length = 433 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TransactionToBeCleared.encode_length, MarketMechanism.encode_length, TradingMode.encode_length, TransactionCategory.encode_length, NegotiationIndicator.encode_length, AgencyCrossIndicator.encode_length, ModificationIndicator.encode_length]

theorem encode_length_pos (message : MifidIiTradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MifidIiTradeReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionToBeCleared.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMechanism.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingMode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NegotiationIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AgencyCrossIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ModificationIndicator.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MifidIiTradeReportMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | loginRequestMessage (message : LoginRequestMessage) -- 1
  | replayRequestMessage (message : ReplayRequestMessage) -- 3
  | loginResponseMessage (message : LoginResponseMessage) -- 2
  | replayResponseMessage (message : ReplayResponseMessage) -- 4
  | replayAndRecoveryCompleteMessage (message : ReplayAndRecoveryCompleteMessage) -- 131
  | systemEventMessage (message : SystemEventMessage) -- 83
  | instrumentDirectoryMessage (message : InstrumentDirectoryMessage) -- 112
  | instrumentStatusMessage (message : InstrumentStatusMessage) -- 72
  | statisticsMessage (message : StatisticsMessage) -- 119
  | mifidIiTradeReportMessage (message : MifidIiTradeReportMessage) -- 84
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .loginRequestMessage _ => 1
  | .replayRequestMessage _ => 3
  | .loginResponseMessage _ => 2
  | .replayResponseMessage _ => 4
  | .replayAndRecoveryCompleteMessage _ => 131
  | .systemEventMessage _ => 83
  | .instrumentDirectoryMessage _ => 112
  | .instrumentStatusMessage _ => 72
  | .statisticsMessage _ => 119
  | .mifidIiTradeReportMessage _ => 84

def encode : Payload → List UInt8
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .replayRequestMessage message => ReplayRequestMessage.encode message
  | .loginResponseMessage message => LoginResponseMessage.encode message
  | .replayResponseMessage message => ReplayResponseMessage.encode message
  | .replayAndRecoveryCompleteMessage message => ReplayAndRecoveryCompleteMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .instrumentDirectoryMessage message => InstrumentDirectoryMessage.encode message
  | .instrumentStatusMessage message => InstrumentStatusMessage.encode message
  | .statisticsMessage message => StatisticsMessage.encode message
  | .mifidIiTradeReportMessage message => MifidIiTradeReportMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 433 := by
  cases message with
  | loginRequestMessage inner =>
    simp only [encode, LoginRequestMessage.encode_length]
    omega
  | replayRequestMessage inner =>
    simp only [encode, ReplayRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [encode, LoginResponseMessage.encode_length]
    omega
  | replayResponseMessage inner =>
    simp only [encode, ReplayResponseMessage.encode_length]
    omega
  | replayAndRecoveryCompleteMessage inner =>
    simp only [encode, ReplayAndRecoveryCompleteMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | instrumentDirectoryMessage inner =>
    simp only [encode, InstrumentDirectoryMessage.encode_length]
    omega
  | instrumentStatusMessage inner =>
    simp only [encode, InstrumentStatusMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [encode, StatisticsMessage.encode_length]
    omega
  | mifidIiTradeReportMessage inner =>
    simp only [encode, MifidIiTradeReportMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (LoginRequestMessage.decode bytes).map fun (message, rest) => (.loginRequestMessage message, rest)
  else if tag = 3 then (ReplayRequestMessage.decode bytes).map fun (message, rest) => (.replayRequestMessage message, rest)
  else if tag = 2 then (LoginResponseMessage.decode bytes).map fun (message, rest) => (.loginResponseMessage message, rest)
  else if tag = 4 then (ReplayResponseMessage.decode bytes).map fun (message, rest) => (.replayResponseMessage message, rest)
  else if tag = 131 then (ReplayAndRecoveryCompleteMessage.decode bytes).map fun (message, rest) => (.replayAndRecoveryCompleteMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 112 then (InstrumentDirectoryMessage.decode bytes).map fun (message, rest) => (.instrumentDirectoryMessage message, rest)
  else if tag = 72 then (InstrumentStatusMessage.decode bytes).map fun (message, rest) => (.instrumentStatusMessage message, rest)
  else if tag = 119 then (StatisticsMessage.decode bytes).map fun (message, rest) => (.statisticsMessage message, rest)
  else if tag = 84 then (MifidIiTradeReportMessage.decode bytes).map fun (message, rest) => (.mifidIiTradeReportMessage message, rest)
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
  | loginRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginRequestMessage.encode_length]
    omega
  | replayRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginResponseMessage.encode_length]
    omega
  | replayResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayResponseMessage.encode_length]
    omega
  | replayAndRecoveryCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayAndRecoveryCompleteMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | instrumentDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InstrumentDirectoryMessage.encode_length]
    omega
  | instrumentStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InstrumentStatusMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsMessage.encode_length]
    omega
  | mifidIiTradeReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MifidIiTradeReportMessage.encode_length]
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

/-- Tcp Unit -/
structure TcpUnit where
  marketDataGroup : Alpha 1
  sequenceNumber : BitVec 32
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace TcpUnit

def encodeBody (message : TcpUnit) : List UInt8 :=
  encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (Alpha.encode message.marketDataGroup
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeMany Message.encode message.message.val)))

def decodeBody (bytes : List UInt8) : Option (TcpUnit × List UInt8) := do
  let (messageCount, bytes) ← decodeUIntLE 1 bytes
  let (marketDataGroup, bytes) ← Alpha.decode 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ marketDataGroup, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem decodeBody_encodeBody (message : TcpUnit) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
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

/-- Size rule: Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : TcpUnit) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (TcpUnit × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : TcpUnit) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : TcpUnit) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end TcpUnit

/-- Packet -/
structure Packet where
  tcpUnit : List TcpUnit
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany TcpUnit.encode message.tcpUnit

def decode (bytes : List UInt8) : Option Packet := do
  let tcpUnit ← decodeAll TcpUnit.decode bytes.length bytes
  pure { tcpUnit }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany TcpUnit.encode TcpUnit.decode TcpUnit.decode_encode TcpUnit.encode_length_pos message.tcpUnit _ (encodeMany_length_ge TcpUnit.encode TcpUnit.encode_length_pos message.tcpUnit), some_bind]
  rfl

end Packet

end Omi.LsegTradeechoMifid2posttradereplayGtpV244
