import Wire

/-!
# New York Stock Exchange Best Quote And Trade v1.7.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseNyseequitiesBqtXdpV17A

/-- Exchange Code: one byte code -/
def ExchangeCode.codes : List UInt8 :=
  [0x41, 0x42, 0x4E, 0x50, 0x51, 0x55, 0x56, 0x5A]

inductive ExchangeCode where
  | nyseAmerican -- Nyse American
  | globalOtc -- Global Otc
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | otcbb -- Otcbb
  | otherOtc -- Other Otc
  | bats -- Bats
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeCode

def toByte : ExchangeCode → UInt8
  | .nyseAmerican => 0x41
  | .globalOtc => 0x42
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .otcbb => 0x55
  | .otherOtc => 0x56
  | .bats => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExchangeCode :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .globalOtc
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x55 then .otcbb
  else if byte = 0x56 then .otherOtc
  else .bats

def ofByte (byte : UInt8) : ExchangeCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeCode) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | globalOtc => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | otcbb => decide
  | otherOtc => decide
  | bats => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExchangeCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExchangeCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExchangeCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExchangeCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExchangeCode

/-- Security Type: one byte code -/
def SecurityType.codes : List UInt8 :=
  [0x41, 0x43, 0x44, 0x45, 0x46, 0x48, 0x49, 0x4C, 0x4D, 0x4F, 0x50, 0x52, 0x53, 0x54, 0x55, 0x57]

inductive SecurityType where
  | adr -- Adr
  | commonStock -- Common Stock
  | debentures -- Debentures
  | etf -- Etf
  | foreign -- Foreign
  | usDepositaryShares -- Us Depositary Shares
  | units -- Units
  | indexLinkedNotes -- Index Linked Notes
  | miscliquidTrust -- Miscliquid Trust
  | ordinaryShares -- Ordinary Shares
  | preferredStock -- Preferred Stock
  | rights -- Rights
  | sharesOfBeneficiaryInterest -- Shares Of Beneficiary Interest
  | test -- Test
  | units_55 -- Units
  | warrant -- Warrant
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityType

def toByte : SecurityType → UInt8
  | .adr => 0x41
  | .commonStock => 0x43
  | .debentures => 0x44
  | .etf => 0x45
  | .foreign => 0x46
  | .usDepositaryShares => 0x48
  | .units => 0x49
  | .indexLinkedNotes => 0x4C
  | .miscliquidTrust => 0x4D
  | .ordinaryShares => 0x4F
  | .preferredStock => 0x50
  | .rights => 0x52
  | .sharesOfBeneficiaryInterest => 0x53
  | .test => 0x54
  | .units_55 => 0x55
  | .warrant => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityType :=
  if byte = 0x41 then .adr
  else if byte = 0x43 then .commonStock
  else if byte = 0x44 then .debentures
  else if byte = 0x45 then .etf
  else if byte = 0x46 then .foreign
  else if byte = 0x48 then .usDepositaryShares
  else if byte = 0x49 then .units
  else if byte = 0x4C then .indexLinkedNotes
  else if byte = 0x4D then .miscliquidTrust
  else if byte = 0x4F then .ordinaryShares
  else if byte = 0x50 then .preferredStock
  else if byte = 0x52 then .rights
  else if byte = 0x53 then .sharesOfBeneficiaryInterest
  else if byte = 0x54 then .test
  else if byte = 0x55 then .units_55
  else .warrant

def ofByte (byte : UInt8) : SecurityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityType) : ofByte value.toByte = value := by
  cases value with
  | adr => decide
  | commonStock => decide
  | debentures => decide
  | etf => decide
  | foreign => decide
  | usDepositaryShares => decide
  | units => decide
  | indexLinkedNotes => decide
  | miscliquidTrust => decide
  | ordinaryShares => decide
  | preferredStock => decide
  | rights => decide
  | sharesOfBeneficiaryInterest => decide
  | test => decide
  | units_55 => decide
  | warrant => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityType

/-- Round Lot: one byte code -/
def RoundLot.codes : List UInt8 :=
  [0x59, 0x4E]

inductive RoundLot where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ RoundLot.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RoundLot

def toByte : RoundLot → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RoundLot :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : RoundLot :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RoundLot) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RoundLot) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RoundLot × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RoundLot) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RoundLot) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RoundLot

/-- Status: one byte code -/
def Status.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]

inductive Status where
  | messageWasAccepted -- Message Was Accepted
  | rejectedDueToAnInvalidSourceId -- Rejected Due To An Invalid Source Id
  | invalidSequenceRange -- Invalid Sequence Range
  | maximumSequenceRange -- Maximum Sequence Range
  | maximumRequestInADay -- Maximum Request In A Day
  | maximumRefreshRequestsInADay -- Maximum Refresh Requests In A Day
  | oldSeqNumTtl -- Old Seq Num Ttl
  | invalidChannelId -- Invalid Channel Id
  | invalidProductId -- Invalid Product Id
  | invalidMsgTypeOrMismatchBetweenMsgTypeAndMsgSize -- Invalid Msg Type Or Mismatch Between Msg Type And Msg Size
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .messageWasAccepted => 0x30
  | .rejectedDueToAnInvalidSourceId => 0x31
  | .invalidSequenceRange => 0x32
  | .maximumSequenceRange => 0x33
  | .maximumRequestInADay => 0x34
  | .maximumRefreshRequestsInADay => 0x35
  | .oldSeqNumTtl => 0x36
  | .invalidChannelId => 0x37
  | .invalidProductId => 0x38
  | .invalidMsgTypeOrMismatchBetweenMsgTypeAndMsgSize => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x30 then .messageWasAccepted
  else if byte = 0x31 then .rejectedDueToAnInvalidSourceId
  else if byte = 0x32 then .invalidSequenceRange
  else if byte = 0x33 then .maximumSequenceRange
  else if byte = 0x34 then .maximumRequestInADay
  else if byte = 0x35 then .maximumRefreshRequestsInADay
  else if byte = 0x36 then .oldSeqNumTtl
  else if byte = 0x37 then .invalidChannelId
  else if byte = 0x38 then .invalidProductId
  else .invalidMsgTypeOrMismatchBetweenMsgTypeAndMsgSize

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | messageWasAccepted => decide
  | rejectedDueToAnInvalidSourceId => decide
  | invalidSequenceRange => decide
  | maximumSequenceRange => decide
  | maximumRequestInADay => decide
  | maximumRefreshRequestsInADay => decide
  | oldSeqNumTtl => decide
  | invalidChannelId => decide
  | invalidProductId => decide
  | invalidMsgTypeOrMismatchBetweenMsgTypeAndMsgSize => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Status) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Status × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Status) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Status) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Status

/-- Security Status: one byte code -/
def SecurityStatus.codes : List UInt8 :=
  [0x33, 0x34, 0x35, 0x36, 0x41, 0x43, 0x44, 0x50, 0x45, 0x4F, 0x4C, 0x58, 0x54, 0x49, 0x47, 0x52]

inductive SecurityStatus where
  | openingDelay -- Opening Delay
  | tradingHalt -- Trading Halt
  | resume -- Resume
  | noOpennoResume -- No Openno Resume
  | shortSaleRestrictionActivatedDay1 -- Short Sale Restriction Activated Day 1
  | shortSaleRestrictionContinuedDay2 -- Short Sale Restriction Continued Day 2
  | shortSaleRestrictionDeactivated -- Short Sale Restriction Deactivated
  | preopening -- Preopening
  | earlySession -- Early Session
  | coreSession -- Core Session
  | lateSessionNonNyseOnly -- Late Session Non Nyse Only
  | closed -- Closed
  | time -- Time
  | priceIndication -- Price Indication
  | preOpeningPriceIndication -- Pre Opening Price Indication
  | rule15Indication -- Rule 15 Indication
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatus

def toByte : SecurityStatus → UInt8
  | .openingDelay => 0x33
  | .tradingHalt => 0x34
  | .resume => 0x35
  | .noOpennoResume => 0x36
  | .shortSaleRestrictionActivatedDay1 => 0x41
  | .shortSaleRestrictionContinuedDay2 => 0x43
  | .shortSaleRestrictionDeactivated => 0x44
  | .preopening => 0x50
  | .earlySession => 0x45
  | .coreSession => 0x4F
  | .lateSessionNonNyseOnly => 0x4C
  | .closed => 0x58
  | .time => 0x54
  | .priceIndication => 0x49
  | .preOpeningPriceIndication => 0x47
  | .rule15Indication => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x33 then .openingDelay
  else if byte = 0x34 then .tradingHalt
  else if byte = 0x35 then .resume
  else if byte = 0x36 then .noOpennoResume
  else if byte = 0x41 then .shortSaleRestrictionActivatedDay1
  else if byte = 0x43 then .shortSaleRestrictionContinuedDay2
  else if byte = 0x44 then .shortSaleRestrictionDeactivated
  else if byte = 0x50 then .preopening
  else if byte = 0x45 then .earlySession
  else if byte = 0x4F then .coreSession
  else if byte = 0x4C then .lateSessionNonNyseOnly
  else if byte = 0x58 then .closed
  else if byte = 0x54 then .time
  else if byte = 0x49 then .priceIndication
  else if byte = 0x47 then .preOpeningPriceIndication
  else .rule15Indication

def ofByte (byte : UInt8) : SecurityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatus) : ofByte value.toByte = value := by
  cases value with
  | openingDelay => decide
  | tradingHalt => decide
  | resume => decide
  | noOpennoResume => decide
  | shortSaleRestrictionActivatedDay1 => decide
  | shortSaleRestrictionContinuedDay2 => decide
  | shortSaleRestrictionDeactivated => decide
  | preopening => decide
  | earlySession => decide
  | coreSession => decide
  | lateSessionNonNyseOnly => decide
  | closed => decide
  | time => decide
  | priceIndication => decide
  | preOpeningPriceIndication => decide
  | rule15Indication => decide
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

/-- Halt Condition: one byte code -/
def HaltCondition.codes : List UInt8 :=
  [0x7E, 0x20, 0x44, 0x49, 0x50, 0x4D, 0x58, 0x5A, 0x31, 0x32, 0x33]

inductive HaltCondition where
  | securityNotDelayedhalted -- Security Not Delayedhalted
  | notApplicable -- Not Applicable
  | newsDissemination -- News Dissemination
  | orderImbalance -- Order Imbalance
  | newsPending -- News Pending
  | volatilityTradingPause -- Volatility Trading Pause
  | equipmentChangeover -- Equipment Changeover
  | noOpenNoResume -- No Open No Resume
  | marketWideCircuitBreakerHaltLevel1 -- Market Wide Circuit Breaker Halt Level 1
  | marketWideCircuitBreakerHaltLevel2 -- Market Wide Circuit Breaker Halt Level 2
  | marketWideCircuitBreakerHaltLevel3 -- Market Wide Circuit Breaker Halt Level 3
  | unlisted (byte : { byte : UInt8 // byte ∉ HaltCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HaltCondition

def toByte : HaltCondition → UInt8
  | .securityNotDelayedhalted => 0x7E
  | .notApplicable => 0x20
  | .newsDissemination => 0x44
  | .orderImbalance => 0x49
  | .newsPending => 0x50
  | .volatilityTradingPause => 0x4D
  | .equipmentChangeover => 0x58
  | .noOpenNoResume => 0x5A
  | .marketWideCircuitBreakerHaltLevel1 => 0x31
  | .marketWideCircuitBreakerHaltLevel2 => 0x32
  | .marketWideCircuitBreakerHaltLevel3 => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HaltCondition :=
  if byte = 0x7E then .securityNotDelayedhalted
  else if byte = 0x20 then .notApplicable
  else if byte = 0x44 then .newsDissemination
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x50 then .newsPending
  else if byte = 0x4D then .volatilityTradingPause
  else if byte = 0x58 then .equipmentChangeover
  else if byte = 0x5A then .noOpenNoResume
  else if byte = 0x31 then .marketWideCircuitBreakerHaltLevel1
  else if byte = 0x32 then .marketWideCircuitBreakerHaltLevel2
  else .marketWideCircuitBreakerHaltLevel3

def ofByte (byte : UInt8) : HaltCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HaltCondition) : ofByte value.toByte = value := by
  cases value with
  | securityNotDelayedhalted => decide
  | notApplicable => decide
  | newsDissemination => decide
  | orderImbalance => decide
  | newsPending => decide
  | volatilityTradingPause => decide
  | equipmentChangeover => decide
  | noOpenNoResume => decide
  | marketWideCircuitBreakerHaltLevel1 => decide
  | marketWideCircuitBreakerHaltLevel2 => decide
  | marketWideCircuitBreakerHaltLevel3 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HaltCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HaltCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HaltCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : HaltCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HaltCondition

/-- Ssr Triggering Exchange Id: one byte code -/
def SsrTriggeringExchangeId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x49, 0x4A, 0x4B, 0x4D, 0x4E, 0x50, 0x51, 0x53, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x20]

inductive SsrTriggeringExchangeId where
  | nyseAmerican -- Nyse American
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nyseNational -- Nyse National
  | finra -- Finra
  | ise -- Ise
  | edga -- Edga
  | edgx -- Edgx
  | chx -- Chx
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | cts -- Cts
  | nasdaqOmx -- Nasdaq Omx
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqOmxPsx -- Nasdaq Omx Psx
  | batsY -- Bats Y
  | bats -- Bats
  | noValue -- No Value
  | unlisted (byte : { byte : UInt8 // byte ∉ SsrTriggeringExchangeId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SsrTriggeringExchangeId

def toByte : SsrTriggeringExchangeId → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqOmxBx => 0x42
  | .nyseNational => 0x43
  | .finra => 0x44
  | .ise => 0x49
  | .edga => 0x4A
  | .edgx => 0x4B
  | .chx => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .cts => 0x53
  | .nasdaqOmx => 0x54
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqOmxPsx => 0x58
  | .batsY => 0x59
  | .bats => 0x5A
  | .noValue => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SsrTriggeringExchangeId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqOmxBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finra
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .edga
  else if byte = 0x4B then .edgx
  else if byte = 0x4D then .chx
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x53 then .cts
  else if byte = 0x54 then .nasdaqOmx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqOmxPsx
  else if byte = 0x59 then .batsY
  else if byte = 0x5A then .bats
  else .noValue

def ofByte (byte : UInt8) : SsrTriggeringExchangeId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SsrTriggeringExchangeId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqOmxBx => decide
  | nyseNational => decide
  | finra => decide
  | ise => decide
  | edga => decide
  | edgx => decide
  | chx => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | cts => decide
  | nasdaqOmx => decide
  | iex => decide
  | cbsx => decide
  | nasdaqOmxPsx => decide
  | batsY => decide
  | bats => decide
  | noValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SsrTriggeringExchangeId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SsrTriggeringExchangeId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SsrTriggeringExchangeId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SsrTriggeringExchangeId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SsrTriggeringExchangeId

/-- Ssr State: one byte code -/
def SsrState.codes : List UInt8 :=
  [0x7E, 0x45]

inductive SsrState where
  | noShortSaleRestrictionInEffect -- No Short Sale Restriction In Effect
  | shortSaleRestrictionInEffect -- Short Sale Restriction In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ SsrState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SsrState

def toByte : SsrState → UInt8
  | .noShortSaleRestrictionInEffect => 0x7E
  | .shortSaleRestrictionInEffect => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SsrState :=
  if byte = 0x7E then .noShortSaleRestrictionInEffect
  else .shortSaleRestrictionInEffect

def ofByte (byte : UInt8) : SsrState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SsrState) : ofByte value.toByte = value := by
  cases value with
  | noShortSaleRestrictionInEffect => decide
  | shortSaleRestrictionInEffect => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SsrState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SsrState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SsrState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SsrState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SsrState

/-- Market State: one byte code -/
def MarketState.codes : List UInt8 :=
  [0x50, 0x45, 0x4F, 0x4C, 0x58]

inductive MarketState where
  | preopening -- Preopening
  | earlySession -- Early Session
  | coreSession -- Core Session
  | lateSession -- Late Session
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketState

def toByte : MarketState → UInt8
  | .preopening => 0x50
  | .earlySession => 0x45
  | .coreSession => 0x4F
  | .lateSession => 0x4C
  | .closed => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketState :=
  if byte = 0x50 then .preopening
  else if byte = 0x45 then .earlySession
  else if byte = 0x4F then .coreSession
  else if byte = 0x4C then .lateSession
  else .closed

def ofByte (byte : UInt8) : MarketState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketState) : ofByte value.toByte = value := by
  cases value with
  | preopening => decide
  | earlySession => decide
  | coreSession => decide
  | lateSession => decide
  | closed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketState

/-- Session State: one byte code -/
def SessionState.codes : List UInt8 :=
  [0x58, 0x59, 0x5A]

inductive SessionState where
  | earlySessionState -- Early Session State
  | coreSessionState -- Core Session State
  | lateSessionState -- Late Session State
  | unlisted (byte : { byte : UInt8 // byte ∉ SessionState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SessionState

def toByte : SessionState → UInt8
  | .earlySessionState => 0x58
  | .coreSessionState => 0x59
  | .lateSessionState => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SessionState :=
  if byte = 0x58 then .earlySessionState
  else if byte = 0x59 then .coreSessionState
  else .lateSessionState

def ofByte (byte : UInt8) : SessionState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SessionState) : ofByte value.toByte = value := by
  cases value with
  | earlySessionState => decide
  | coreSessionState => decide
  | lateSessionState => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SessionState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SessionState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SessionState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SessionState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SessionState

/-- Ask Quote Condition: one byte code -/
def AskQuoteCondition.codes : List UInt8 :=
  [0x43, 0x4F, 0x52, 0x57]

inductive AskQuoteCondition where
  | closing -- Closing
  | openingQuote -- Opening Quote
  | regularQuote -- Regular Quote
  | slowOnTheBidAndAsk -- Slow On The Bid And Ask
  | unlisted (byte : { byte : UInt8 // byte ∉ AskQuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AskQuoteCondition

def toByte : AskQuoteCondition → UInt8
  | .closing => 0x43
  | .openingQuote => 0x4F
  | .regularQuote => 0x52
  | .slowOnTheBidAndAsk => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AskQuoteCondition :=
  if byte = 0x43 then .closing
  else if byte = 0x4F then .openingQuote
  else if byte = 0x52 then .regularQuote
  else .slowOnTheBidAndAsk

def ofByte (byte : UInt8) : AskQuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AskQuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | closing => decide
  | openingQuote => decide
  | regularQuote => decide
  | slowOnTheBidAndAsk => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AskQuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AskQuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AskQuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AskQuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AskQuoteCondition

/-- Bid Quote Condition: one byte code -/
def BidQuoteCondition.codes : List UInt8 :=
  [0x43, 0x4F, 0x52, 0x57]

inductive BidQuoteCondition where
  | closing -- Closing
  | openingQuote -- Opening Quote
  | regularQuote -- Regular Quote
  | slowOnTheBidAndAsk -- Slow On The Bid And Ask
  | unlisted (byte : { byte : UInt8 // byte ∉ BidQuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BidQuoteCondition

def toByte : BidQuoteCondition → UInt8
  | .closing => 0x43
  | .openingQuote => 0x4F
  | .regularQuote => 0x52
  | .slowOnTheBidAndAsk => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BidQuoteCondition :=
  if byte = 0x43 then .closing
  else if byte = 0x4F then .openingQuote
  else if byte = 0x52 then .regularQuote
  else .slowOnTheBidAndAsk

def ofByte (byte : UInt8) : BidQuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BidQuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | closing => decide
  | openingQuote => decide
  | regularQuote => decide
  | slowOnTheBidAndAsk => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BidQuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BidQuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BidQuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BidQuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BidQuoteCondition

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

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x43, 0x4F, 0x52, 0x57]

inductive QuoteCondition where
  | closing -- Closing
  | openingQuote -- Opening Quote
  | regularQuote -- Regular Quote
  | slowOnTheBidAndAsk -- Slow On The Bid And Ask
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .closing => 0x43
  | .openingQuote => 0x4F
  | .regularQuote => 0x52
  | .slowOnTheBidAndAsk => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x43 then .closing
  else if byte = 0x4F then .openingQuote
  else if byte = 0x52 then .regularQuote
  else .slowOnTheBidAndAsk

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | closing => decide
  | openingQuote => decide
  | regularQuote => decide
  | slowOnTheBidAndAsk => decide
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

/-- Rpi Indicator: one byte code -/
def RpiIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43]

inductive RpiIndicator where
  | noRetailInterest -- No Retail Interest
  | interestOnBid -- Interest On Bid
  | interestOnOffer -- Interest On Offer
  | interestOnBidAndOffer -- Interest On Bid And Offer
  | unlisted (byte : { byte : UInt8 // byte ∉ RpiIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RpiIndicator

def toByte : RpiIndicator → UInt8
  | .noRetailInterest => 0x20
  | .interestOnBid => 0x41
  | .interestOnOffer => 0x42
  | .interestOnBidAndOffer => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RpiIndicator :=
  if byte = 0x20 then .noRetailInterest
  else if byte = 0x41 then .interestOnBid
  else if byte = 0x42 then .interestOnOffer
  else .interestOnBidAndOffer

def ofByte (byte : UInt8) : RpiIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RpiIndicator) : ofByte value.toByte = value := by
  cases value with
  | noRetailInterest => decide
  | interestOnBid => decide
  | interestOnOffer => decide
  | interestOnBidAndOffer => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RpiIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RpiIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RpiIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RpiIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RpiIndicator

/-- Trade Condition 1: one byte code -/
def TradeCondition1.codes : List UInt8 :=
  [0x40, 0x43, 0x4E, 0x52]

inductive TradeCondition1 where
  | regularSale -- Regular Sale
  | cash -- Cash
  | nextDayTrade -- Next Day Trade
  | seller -- Seller
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCondition1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCondition1

def toByte : TradeCondition1 → UInt8
  | .regularSale => 0x40
  | .cash => 0x43
  | .nextDayTrade => 0x4E
  | .seller => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCondition1 :=
  if byte = 0x40 then .regularSale
  else if byte = 0x43 then .cash
  else if byte = 0x4E then .nextDayTrade
  else .seller

def ofByte (byte : UInt8) : TradeCondition1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCondition1) : ofByte value.toByte = value := by
  cases value with
  | regularSale => decide
  | cash => decide
  | nextDayTrade => decide
  | seller => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCondition1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCondition1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCondition1) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCondition1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCondition1

/-- Trade Condition 2: one byte code -/
def TradeCondition2.codes : List UInt8 :=
  [0x20, 0x46, 0x4F, 0x34, 0x35, 0x36, 0x39]

inductive TradeCondition2 where
  | na -- Na
  | intermarketSweepOrder -- Intermarket Sweep Order
  | marketCenterOpeningTrade -- Market Center Opening Trade
  | derivativelyPriced -- Derivatively Priced
  | marketCenterReopeningTrade -- Market Center Reopening Trade
  | marketCenterClosingTrade -- Market Center Closing Trade
  | correctedLastSalePrice -- Corrected Last Sale Price
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCondition2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCondition2

def toByte : TradeCondition2 → UInt8
  | .na => 0x20
  | .intermarketSweepOrder => 0x46
  | .marketCenterOpeningTrade => 0x4F
  | .derivativelyPriced => 0x34
  | .marketCenterReopeningTrade => 0x35
  | .marketCenterClosingTrade => 0x36
  | .correctedLastSalePrice => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCondition2 :=
  if byte = 0x20 then .na
  else if byte = 0x46 then .intermarketSweepOrder
  else if byte = 0x4F then .marketCenterOpeningTrade
  else if byte = 0x34 then .derivativelyPriced
  else if byte = 0x35 then .marketCenterReopeningTrade
  else if byte = 0x36 then .marketCenterClosingTrade
  else .correctedLastSalePrice

def ofByte (byte : UInt8) : TradeCondition2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCondition2) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | intermarketSweepOrder => decide
  | marketCenterOpeningTrade => decide
  | derivativelyPriced => decide
  | marketCenterReopeningTrade => decide
  | marketCenterClosingTrade => decide
  | correctedLastSalePrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCondition2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCondition2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCondition2) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCondition2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCondition2

/-- Trade Condition 3: one byte code -/
def TradeCondition3.codes : List UInt8 :=
  [0x20, 0x4C, 0x54, 0x55, 0x5A]

inductive TradeCondition3 where
  | na -- Na
  | soldLast -- Sold Last
  | extendedHoursTrade -- Extended Hours Trade
  | extendedHoursSoldOutOfSequence -- Extended Hours Sold Out Of Sequence
  | sold -- Sold
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCondition3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCondition3

def toByte : TradeCondition3 → UInt8
  | .na => 0x20
  | .soldLast => 0x4C
  | .extendedHoursTrade => 0x54
  | .extendedHoursSoldOutOfSequence => 0x55
  | .sold => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCondition3 :=
  if byte = 0x20 then .na
  else if byte = 0x4C then .soldLast
  else if byte = 0x54 then .extendedHoursTrade
  else if byte = 0x55 then .extendedHoursSoldOutOfSequence
  else .sold

def ofByte (byte : UInt8) : TradeCondition3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCondition3) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | soldLast => decide
  | extendedHoursTrade => decide
  | extendedHoursSoldOutOfSequence => decide
  | sold => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCondition3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCondition3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCondition3) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCondition3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCondition3

/-- Trade Condition 4: one byte code -/
def TradeCondition4.codes : List UInt8 :=
  [0x20, 0x40, 0x42, 0x45, 0x48, 0x49, 0x4B, 0x4D, 0x50, 0x51, 0x56, 0x58]

inductive TradeCondition4 where
  | na -- Na
  | regularSale -- Regular Sale
  | averagePriceTrade -- Average Price Trade
  | automaticExecution -- Automatic Execution
  | priceVariationTrade -- Price Variation Trade
  | oddLotTrade -- Odd Lot Trade
  | rule127NyseOnlyOrRule155NyseAmericanOnly -- Rule 127 Nyse Only Or Rule 155 Nyse American Only
  | officialClosingPrice -- Official Closing Price
  | priorReferencePrice -- Prior Reference Price
  | officialOpenPrice -- Official Open Price
  | stockOptionTrade -- Stock Option Trade
  | crossTrade -- Cross Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCondition4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCondition4

def toByte : TradeCondition4 → UInt8
  | .na => 0x20
  | .regularSale => 0x40
  | .averagePriceTrade => 0x42
  | .automaticExecution => 0x45
  | .priceVariationTrade => 0x48
  | .oddLotTrade => 0x49
  | .rule127NyseOnlyOrRule155NyseAmericanOnly => 0x4B
  | .officialClosingPrice => 0x4D
  | .priorReferencePrice => 0x50
  | .officialOpenPrice => 0x51
  | .stockOptionTrade => 0x56
  | .crossTrade => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCondition4 :=
  if byte = 0x20 then .na
  else if byte = 0x40 then .regularSale
  else if byte = 0x42 then .averagePriceTrade
  else if byte = 0x45 then .automaticExecution
  else if byte = 0x48 then .priceVariationTrade
  else if byte = 0x49 then .oddLotTrade
  else if byte = 0x4B then .rule127NyseOnlyOrRule155NyseAmericanOnly
  else if byte = 0x4D then .officialClosingPrice
  else if byte = 0x50 then .priorReferencePrice
  else if byte = 0x51 then .officialOpenPrice
  else if byte = 0x56 then .stockOptionTrade
  else .crossTrade

def ofByte (byte : UInt8) : TradeCondition4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCondition4) : ofByte value.toByte = value := by
  cases value with
  | na => decide
  | regularSale => decide
  | averagePriceTrade => decide
  | automaticExecution => decide
  | priceVariationTrade => decide
  | oddLotTrade => decide
  | rule127NyseOnlyOrRule155NyseAmericanOnly => decide
  | officialClosingPrice => decide
  | priorReferencePrice => decide
  | officialOpenPrice => decide
  | stockOptionTrade => decide
  | crossTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCondition4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCondition4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCondition4) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeCondition4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCondition4

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

/-- Symbol Index Mapping Message: 40 bytes -/
structure SymbolIndexMappingMessage where
  symbolIndex : BitVec 32
  symbol : Alpha 11
  reserved1 : Alpha 1
  marketId : BitVec 16
  systemId : BitVec 8
  exchangeCode : ExchangeCode
  priceScaleCode : BitVec 8
  securityType : SecurityType
  lotSize : BitVec 16
  prevClosePrice : BitVec 32
  prevCloseVolume : BitVec 32
  priceResolution : BitVec 8
  roundLot : RoundLot
  mpv : BitVec 16
  unitOfTrade : BitVec 16
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace SymbolIndexMappingMessage

def encode (message : SymbolIndexMappingMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUIntLE 1 message.systemId
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (encodeUIntLE 1 message.priceScaleCode
    ++ (SecurityType.encode message.securityType
    ++ (encodeUIntLE 2 message.lotSize
    ++ (encodeUIntLE 4 message.prevClosePrice
    ++ (encodeUIntLE 4 message.prevCloseVolume
    ++ (encodeUIntLE 1 message.priceResolution
    ++ (RoundLot.encode message.roundLot
    ++ (encodeUIntLE 2 message.mpv
    ++ (encodeUIntLE 2 message.unitOfTrade
    ++ (Alpha.encode message.reserved2)))))))))))))))

def decode (bytes : List UInt8) : Option (SymbolIndexMappingMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 11 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (systemId, bytes) ← decodeUIntLE 1 bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (priceScaleCode, bytes) ← decodeUIntLE 1 bytes
  let (securityType, bytes) ← SecurityType.decode bytes
  let (lotSize, bytes) ← decodeUIntLE 2 bytes
  let (prevClosePrice, bytes) ← decodeUIntLE 4 bytes
  let (prevCloseVolume, bytes) ← decodeUIntLE 4 bytes
  let (priceResolution, bytes) ← decodeUIntLE 1 bytes
  let (roundLot, bytes) ← RoundLot.decode bytes
  let (mpv, bytes) ← decodeUIntLE 2 bytes
  let (unitOfTrade, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ symbolIndex, symbol, reserved1, marketId, systemId, exchangeCode, priceScaleCode, securityType, lotSize, prevClosePrice, prevCloseVolume, priceResolution, roundLot, mpv, unitOfTrade, reserved2 }, bytes)

@[simp] theorem encode_length (message : SymbolIndexMappingMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ExchangeCode.encode_length, SecurityType.encode_length, RoundLot.encode_length]

theorem encode_length_pos (message : SymbolIndexMappingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolIndexMappingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, RoundLot.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolIndexMappingMessage

/-- Retransmission Request Message: 20 bytes -/
structure RetransmissionRequestMessage where
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  sourceId : Alpha 10
  productId : BitVec 8
  channelId : BitVec 8
  deriving DecidableEq, Repr

namespace RetransmissionRequestMessage

def encode (message : RetransmissionRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.beginSeqNum
    ++ (encodeUIntLE 4 message.endSeqNum
    ++ (Alpha.encode message.sourceId
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId))))

def decode (bytes : List UInt8) : Option (RetransmissionRequestMessage × List UInt8) := do
  let (beginSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (sourceId, bytes) ← Alpha.decode 10 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  pure ({ beginSeqNum, endSeqNum, sourceId, productId, channelId }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequestMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RetransmissionRequestMessage

/-- Request Response Message: 25 bytes -/
structure RequestResponseMessage where
  requestSeqNum : BitVec 32
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  sourceId : Alpha 10
  productId : BitVec 8
  channelId : BitVec 8
  status : Status
  deriving DecidableEq, Repr

namespace RequestResponseMessage

def encode (message : RequestResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.requestSeqNum
    ++ (encodeUIntLE 4 message.beginSeqNum
    ++ (encodeUIntLE 4 message.endSeqNum
    ++ (Alpha.encode message.sourceId
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId
    ++ (Status.encode message.status))))))

def decode (bytes : List UInt8) : Option (RequestResponseMessage × List UInt8) := do
  let (requestSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (beginSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (sourceId, bytes) ← Alpha.decode 10 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  let (status, bytes) ← Status.decode bytes
  pure ({ requestSeqNum, beginSeqNum, endSeqNum, sourceId, productId, channelId, status }, bytes)

@[simp] theorem encode_length (message : RequestResponseMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Status.encode_length]

theorem encode_length_pos (message : RequestResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Status.decode_encode, some_bind]
  rfl

end RequestResponseMessage

/-- Heartbeat Response Message: 10 bytes -/
structure HeartbeatResponseMessage where
  sourceId : Alpha 10
  deriving DecidableEq, Repr

namespace HeartbeatResponseMessage

def encode (message : HeartbeatResponseMessage) : List UInt8 :=
  Alpha.encode message.sourceId

def decode (bytes : List UInt8) : Option (HeartbeatResponseMessage × List UInt8) := do
  let (sourceId, bytes) ← Alpha.decode 10 bytes
  pure ({ sourceId }, bytes)

@[simp] theorem encode_length (message : HeartbeatResponseMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : HeartbeatResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end HeartbeatResponseMessage

/-- Symbol Index Mapping Request Message: 17 bytes -/
structure SymbolIndexMappingRequestMessage where
  symbolIndex : BitVec 32
  sourceId : Alpha 10
  productId : BitVec 8
  channelId : BitVec 8
  retransmitMethod : BitVec 8
  deriving DecidableEq, Repr

namespace SymbolIndexMappingRequestMessage

def encode (message : SymbolIndexMappingRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (Alpha.encode message.sourceId
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId
    ++ (encodeUIntLE 1 message.retransmitMethod))))

def decode (bytes : List UInt8) : Option (SymbolIndexMappingRequestMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (sourceId, bytes) ← Alpha.decode 10 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  let (retransmitMethod, bytes) ← decodeUIntLE 1 bytes
  pure ({ symbolIndex, sourceId, productId, channelId, retransmitMethod }, bytes)

@[simp] theorem encode_length (message : SymbolIndexMappingRequestMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SymbolIndexMappingRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolIndexMappingRequestMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SymbolIndexMappingRequestMessage

/-- Refresh Request Message: 16 bytes -/
structure RefreshRequestMessage where
  symbolIndex : BitVec 32
  sourceId : Alpha 10
  productId : BitVec 8
  channelId : BitVec 8
  deriving DecidableEq, Repr

namespace RefreshRequestMessage

def encode (message : RefreshRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (Alpha.encode message.sourceId
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId)))

def decode (bytes : List UInt8) : Option (RefreshRequestMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (sourceId, bytes) ← Alpha.decode 10 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  pure ({ symbolIndex, sourceId, productId, channelId }, bytes)

@[simp] theorem encode_length (message : RefreshRequestMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RefreshRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RefreshRequestMessage

/-- Message Unavailable Message: 10 bytes -/
structure MessageUnavailableMessage where
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  productId : BitVec 8
  channelId : BitVec 8
  deriving DecidableEq, Repr

namespace MessageUnavailableMessage

def encode (message : MessageUnavailableMessage) : List UInt8 :=
  encodeUIntLE 4 message.beginSeqNum
    ++ (encodeUIntLE 4 message.endSeqNum
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId)))

def decode (bytes : List UInt8) : Option (MessageUnavailableMessage × List UInt8) := do
  let (beginSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  pure ({ beginSeqNum, endSeqNum, productId, channelId }, bytes)

@[simp] theorem encode_length (message : MessageUnavailableMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MessageUnavailableMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageUnavailableMessage) (rest : List UInt8) :
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

end MessageUnavailableMessage

/-- Consolidated Symbol Clear Message: 18 bytes -/
structure ConsolidatedSymbolClearMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  nextSourceSeqNum : BitVec 32
  marketId : BitVec 16
  deriving DecidableEq, Repr

namespace ConsolidatedSymbolClearMessage

def encode (message : ConsolidatedSymbolClearMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.nextSourceSeqNum
    ++ (encodeUIntLE 2 message.marketId))))

def decode (bytes : List UInt8) : Option (ConsolidatedSymbolClearMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (nextSourceSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, nextSourceSeqNum, marketId }, bytes)

@[simp] theorem encode_length (message : ConsolidatedSymbolClearMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ConsolidatedSymbolClearMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedSymbolClearMessage) (rest : List UInt8) :
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

end ConsolidatedSymbolClearMessage

/-- Consolidated Trading Session Change Message: 19 bytes -/
structure ConsolidatedTradingSessionChangeMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  tradeSession : BitVec 8
  marketId : BitVec 16
  deriving DecidableEq, Repr

namespace ConsolidatedTradingSessionChangeMessage

def encode (message : ConsolidatedTradingSessionChangeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 1 message.tradeSession
    ++ (encodeUIntLE 2 message.marketId)))))

def decode (bytes : List UInt8) : Option (ConsolidatedTradingSessionChangeMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (tradeSession, bytes) ← decodeUIntLE 1 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, tradeSession, marketId }, bytes)

@[simp] theorem encode_length (message : ConsolidatedTradingSessionChangeMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ConsolidatedTradingSessionChangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedTradingSessionChangeMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConsolidatedTradingSessionChangeMessage

/-- Consolidated Security Status Message: 42 bytes -/
structure ConsolidatedSecurityStatusMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  securityStatus : SecurityStatus
  haltCondition : HaltCondition
  marketId : BitVec 16
  reserved2 : Alpha 2
  price1 : BitVec 32
  price2 : BitVec 32
  ssrTriggeringExchangeId : SsrTriggeringExchangeId
  ssrTriggeringVolume : BitVec 32
  time : BitVec 32
  ssrState : SsrState
  marketState : MarketState
  sessionState : SessionState
  deriving DecidableEq, Repr

namespace ConsolidatedSecurityStatusMessage

def encode (message : ConsolidatedSecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (SecurityStatus.encode message.securityStatus
    ++ (HaltCondition.encode message.haltCondition
    ++ (encodeUIntLE 2 message.marketId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUIntLE 4 message.price1
    ++ (encodeUIntLE 4 message.price2
    ++ (SsrTriggeringExchangeId.encode message.ssrTriggeringExchangeId
    ++ (encodeUIntLE 4 message.ssrTriggeringVolume
    ++ (encodeUIntLE 4 message.time
    ++ (SsrState.encode message.ssrState
    ++ (MarketState.encode message.marketState
    ++ (SessionState.encode message.sessionState)))))))))))))))

def decode (bytes : List UInt8) : Option (ConsolidatedSecurityStatusMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (haltCondition, bytes) ← HaltCondition.decode bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (price1, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 4 bytes
  let (ssrTriggeringExchangeId, bytes) ← SsrTriggeringExchangeId.decode bytes
  let (ssrTriggeringVolume, bytes) ← decodeUIntLE 4 bytes
  let (time, bytes) ← decodeUIntLE 4 bytes
  let (ssrState, bytes) ← SsrState.decode bytes
  let (marketState, bytes) ← MarketState.decode bytes
  let (sessionState, bytes) ← SessionState.decode bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, securityStatus, haltCondition, marketId, reserved2, price1, price2, ssrTriggeringExchangeId, ssrTriggeringVolume, time, ssrState, marketState, sessionState }, bytes)

@[simp] theorem encode_length (message : ConsolidatedSecurityStatusMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityStatus.encode_length, HaltCondition.encode_length, Alpha.encode_length, SsrTriggeringExchangeId.encode_length, SsrState.encode_length, MarketState.encode_length, SessionState.encode_length]

theorem encode_length_pos (message : ConsolidatedSecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedSecurityStatusMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, HaltCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SsrTriggeringExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SsrState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketState.decode_encode, some_bind]
  dsimp only
  rw [SessionState.decode_encode, some_bind]
  rfl

end ConsolidatedSecurityStatusMessage

/-- Full Refresh Header: 8 bytes -/
structure FullRefreshHeader where
  lastSeqNum : BitVec 32
  lastSymbolSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace FullRefreshHeader

def encode (message : FullRefreshHeader) : List UInt8 :=
  encodeUIntLE 4 message.lastSeqNum
    ++ (encodeUIntLE 4 message.lastSymbolSeqNum)

def decode (bytes : List UInt8) : Option (FullRefreshHeader × List UInt8) := do
  let (lastSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (lastSymbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ lastSeqNum, lastSymbolSeqNum }, bytes)

@[simp] theorem encode_length (message : FullRefreshHeader) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : FullRefreshHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FullRefreshHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end FullRefreshHeader

/-- Any Refresh Header Layout, selected by Current Refresh Pkt -/
inductive RefreshHeaderLayout where
  | fullRefreshHeader (message : FullRefreshHeader) -- 1
  | shortRefreshHeader (tag : { v : BitVec 16 // v ≠ 1 }) -- any other value, read as nothing
  deriving DecidableEq, Repr

namespace RefreshHeaderLayout

/-- The Current Refresh Pkt each message is sent under -/
def tag : RefreshHeaderLayout → BitVec 16
  | .fullRefreshHeader _ => 1
  | .shortRefreshHeader tag => tag.val

def encode : RefreshHeaderLayout → List UInt8
  | .fullRefreshHeader message => FullRefreshHeader.encode message
  | .shortRefreshHeader _ => []

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : RefreshHeaderLayout) : (encode message).length ≤ 8 := by
  cases message with
  | fullRefreshHeader inner =>
    simp only [encode, FullRefreshHeader.encode_length]
    omega
  | shortRefreshHeader _ =>
    simp only [encode, List.length_nil]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (RefreshHeaderLayout × List UInt8) :=
  if h0 : tag = 1 then (FullRefreshHeader.decode bytes).map fun (message, rest) => (.fullRefreshHeader message, rest)
  else some (.shortRefreshHeader ⟨tag, h0⟩, bytes)

@[simp] theorem decode_encode (message : RefreshHeaderLayout) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message with
  | fullRefreshHeader m => simp [decode, encode, tag]
  | shortRefreshHeader t =>
    obtain ⟨v, h0⟩ := t
    simp only [tag, encode, decode, h0, List.nil_append, reduceDIte]

end RefreshHeaderLayout

/-- Refresh Header Message -/
structure RefreshHeaderMessage where
  totalRefreshPkts : BitVec 16
  refreshHeaderLayout : RefreshHeaderLayout
  deriving DecidableEq, Repr

namespace RefreshHeaderMessage

def encode (message : RefreshHeaderMessage) : List UInt8 :=
  encodeUIntLE 2 (RefreshHeaderLayout.tag message.refreshHeaderLayout)
    ++ (encodeUIntLE 2 message.totalRefreshPkts
    ++ (RefreshHeaderLayout.encode message.refreshHeaderLayout))

def decode (bytes : List UInt8) : Option (RefreshHeaderMessage × List UInt8) := do
  let (currentRefreshPkt, bytes) ← decodeUIntLE 2 bytes
  let (totalRefreshPkts, bytes) ← decodeUIntLE 2 bytes
  let (refreshHeaderLayout, bytes) ← RefreshHeaderLayout.decode currentRefreshPkt bytes
  pure ({ totalRefreshPkts, refreshHeaderLayout }, bytes)

theorem encode_length_pos (message : RefreshHeaderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RefreshHeaderMessage) : (encode message).length ≤ 12 := by
  unfold encode
  cases message.refreshHeaderLayout with
  | fullRefreshHeader inner =>
    simp only [RefreshHeaderLayout.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, FullRefreshHeader.encode_length]
    omega
  | shortRefreshHeader _ =>
    simp only [RefreshHeaderLayout.encode, List.length_nil, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega

@[simp] theorem decode_encode (message : RefreshHeaderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [RefreshHeaderLayout.decode_encode, some_bind]
  rfl

end RefreshHeaderMessage

/-- Bqt Message: 31 bytes -/
structure BqtMessage where
  symbolIndex : BitVec 32
  symbolSeqNumber : BitVec 32
  askPrice : BitVec 32
  askVolume : BitVec 32
  bidPrice : BitVec 32
  bidVolume : BitVec 32
  askQuoteCondition : AskQuoteCondition
  bidQuoteCondition : BidQuoteCondition
  retailPricingIndicator : BitVec 8
  marketIdOfBestAsk : BitVec 16
  marketIdOfBestBid : BitVec 16
  deriving DecidableEq, Repr

namespace BqtMessage

def encode (message : BqtMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNumber
    ++ (encodeUIntLE 4 message.askPrice
    ++ (encodeUIntLE 4 message.askVolume
    ++ (encodeUIntLE 4 message.bidPrice
    ++ (encodeUIntLE 4 message.bidVolume
    ++ (AskQuoteCondition.encode message.askQuoteCondition
    ++ (BidQuoteCondition.encode message.bidQuoteCondition
    ++ (encodeUIntLE 1 message.retailPricingIndicator
    ++ (encodeUIntLE 2 message.marketIdOfBestAsk
    ++ (encodeUIntLE 2 message.marketIdOfBestBid))))))))))

def decode (bytes : List UInt8) : Option (BqtMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNumber, bytes) ← decodeUIntLE 4 bytes
  let (askPrice, bytes) ← decodeUIntLE 4 bytes
  let (askVolume, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 4 bytes
  let (bidVolume, bytes) ← decodeUIntLE 4 bytes
  let (askQuoteCondition, bytes) ← AskQuoteCondition.decode bytes
  let (bidQuoteCondition, bytes) ← BidQuoteCondition.decode bytes
  let (retailPricingIndicator, bytes) ← decodeUIntLE 1 bytes
  let (marketIdOfBestAsk, bytes) ← decodeUIntLE 2 bytes
  let (marketIdOfBestBid, bytes) ← decodeUIntLE 2 bytes
  pure ({ symbolIndex, symbolSeqNumber, askPrice, askVolume, bidPrice, bidVolume, askQuoteCondition, bidQuoteCondition, retailPricingIndicator, marketIdOfBestAsk, marketIdOfBestBid }, bytes)

@[simp] theorem encode_length (message : BqtMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, AskQuoteCondition.encode_length, BidQuoteCondition.encode_length]

theorem encode_length_pos (message : BqtMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BqtMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, AskQuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidQuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BqtMessage

/-- Consolidated Single Sided Quote Message: 21 bytes -/
structure ConsolidatedSingleSidedQuoteMessage where
  symbolIndex : BitVec 32
  symbolSeqNumber : BitVec 32
  side : Side
  price : BitVec 32
  volume : BitVec 32
  quoteCondition : QuoteCondition
  rpiIndicator : RpiIndicator
  marketId : BitVec 16
  deriving DecidableEq, Repr

namespace ConsolidatedSingleSidedQuoteMessage

def encode (message : ConsolidatedSingleSidedQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNumber
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (RpiIndicator.encode message.rpiIndicator
    ++ (encodeUIntLE 2 message.marketId)))))))

def decode (bytes : List UInt8) : Option (ConsolidatedSingleSidedQuoteMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNumber, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (rpiIndicator, bytes) ← RpiIndicator.decode bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  pure ({ symbolIndex, symbolSeqNumber, side, price, volume, quoteCondition, rpiIndicator, marketId }, bytes)

@[simp] theorem encode_length (message : ConsolidatedSingleSidedQuoteMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, QuoteCondition.encode_length, RpiIndicator.encode_length]

theorem encode_length_pos (message : ConsolidatedSingleSidedQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedSingleSidedQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RpiIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConsolidatedSingleSidedQuoteMessage

/-- Consolidated Trade Message: 34 bytes -/
structure ConsolidatedTradeMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  tradeCondition1 : TradeCondition1
  tradeCondition2 : TradeCondition2
  tradeCondition3 : TradeCondition3
  tradeCondition4 : TradeCondition4
  marketId : BitVec 16
  deriving DecidableEq, Repr

namespace ConsolidatedTradeMessage

def encode (message : ConsolidatedTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (TradeCondition1.encode message.tradeCondition1
    ++ (TradeCondition2.encode message.tradeCondition2
    ++ (TradeCondition3.encode message.tradeCondition3
    ++ (TradeCondition4.encode message.tradeCondition4
    ++ (encodeUIntLE 2 message.marketId)))))))))))

def decode (bytes : List UInt8) : Option (ConsolidatedTradeMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (tradeCondition1, bytes) ← TradeCondition1.decode bytes
  let (tradeCondition2, bytes) ← TradeCondition2.decode bytes
  let (tradeCondition3, bytes) ← TradeCondition3.decode bytes
  let (tradeCondition4, bytes) ← TradeCondition4.decode bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, tradeId, price, volume, tradeCondition1, tradeCondition2, tradeCondition3, tradeCondition4, marketId }, bytes)

@[simp] theorem encode_length (message : ConsolidatedTradeMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCondition1.encode_length, TradeCondition2.encode_length, TradeCondition3.encode_length, TradeCondition4.encode_length]

theorem encode_length_pos (message : ConsolidatedTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeCondition1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCondition2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCondition3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCondition4.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConsolidatedTradeMessage

/-- Consolidated Trade Cancel Message: 22 bytes -/
structure ConsolidatedTradeCancelMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNumber : BitVec 32
  tradeId : BitVec 32
  marketId : BitVec 16
  deriving DecidableEq, Repr

namespace ConsolidatedTradeCancelMessage

def encode (message : ConsolidatedTradeCancelMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNumber
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 2 message.marketId)))))

def decode (bytes : List UInt8) : Option (ConsolidatedTradeCancelMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNumber, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNumber, tradeId, marketId }, bytes)

@[simp] theorem encode_length (message : ConsolidatedTradeCancelMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ConsolidatedTradeCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedTradeCancelMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConsolidatedTradeCancelMessage

/-- Consolidated Trade Correction Message: 38 bytes -/
structure ConsolidatedTradeCorrectionMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNumber : BitVec 32
  originalTradeId : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  tradeCondition1 : TradeCondition1
  tradeCondition2 : TradeCondition2
  tradeCondition3 : TradeCondition3
  tradeCondition4 : TradeCondition4
  marketId : BitVec 16
  deriving DecidableEq, Repr

namespace ConsolidatedTradeCorrectionMessage

def encode (message : ConsolidatedTradeCorrectionMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNumber
    ++ (encodeUIntLE 4 message.originalTradeId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (TradeCondition1.encode message.tradeCondition1
    ++ (TradeCondition2.encode message.tradeCondition2
    ++ (TradeCondition3.encode message.tradeCondition3
    ++ (TradeCondition4.encode message.tradeCondition4
    ++ (encodeUIntLE 2 message.marketId))))))))))))

def decode (bytes : List UInt8) : Option (ConsolidatedTradeCorrectionMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNumber, bytes) ← decodeUIntLE 4 bytes
  let (originalTradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (tradeCondition1, bytes) ← TradeCondition1.decode bytes
  let (tradeCondition2, bytes) ← TradeCondition2.decode bytes
  let (tradeCondition3, bytes) ← TradeCondition3.decode bytes
  let (tradeCondition4, bytes) ← TradeCondition4.decode bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNumber, originalTradeId, tradeId, price, volume, tradeCondition1, tradeCondition2, tradeCondition3, tradeCondition4, marketId }, bytes)

@[simp] theorem encode_length (message : ConsolidatedTradeCorrectionMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCondition1.encode_length, TradeCondition2.encode_length, TradeCondition3.encode_length, TradeCondition4.encode_length]

theorem encode_length_pos (message : ConsolidatedTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedTradeCorrectionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeCondition1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCondition2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCondition3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCondition4.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConsolidatedTradeCorrectionMessage

/-- Consolidated Stock Summary Message: 41 bytes -/
structure ConsolidatedStockSummaryMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  highPrice : BitVec 32
  lowPrice : BitVec 32
  open_ : BitVec 32
  totalVolume : BitVec 32
  marketIdOfHighPrice : BitVec 16
  marketIdOfLowPrice : BitVec 16
  marketIdOfOpenPrice : BitVec 16
  numClosePrices : BitVec 8
  marketIdOfTheClose : BitVec 16
  close : BitVec 32
  deriving DecidableEq, Repr

namespace ConsolidatedStockSummaryMessage

def encode (message : ConsolidatedStockSummaryMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.highPrice
    ++ (encodeUIntLE 4 message.lowPrice
    ++ (encodeUIntLE 4 message.open_
    ++ (encodeUIntLE 4 message.totalVolume
    ++ (encodeUIntLE 2 message.marketIdOfHighPrice
    ++ (encodeUIntLE 2 message.marketIdOfLowPrice
    ++ (encodeUIntLE 2 message.marketIdOfOpenPrice
    ++ (encodeUIntLE 1 message.numClosePrices
    ++ (encodeUIntLE 2 message.marketIdOfTheClose
    ++ (encodeUIntLE 4 message.close))))))))))))

def decode (bytes : List UInt8) : Option (ConsolidatedStockSummaryMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (highPrice, bytes) ← decodeUIntLE 4 bytes
  let (lowPrice, bytes) ← decodeUIntLE 4 bytes
  let (open_, bytes) ← decodeUIntLE 4 bytes
  let (totalVolume, bytes) ← decodeUIntLE 4 bytes
  let (marketIdOfHighPrice, bytes) ← decodeUIntLE 2 bytes
  let (marketIdOfLowPrice, bytes) ← decodeUIntLE 2 bytes
  let (marketIdOfOpenPrice, bytes) ← decodeUIntLE 2 bytes
  let (numClosePrices, bytes) ← decodeUIntLE 1 bytes
  let (marketIdOfTheClose, bytes) ← decodeUIntLE 2 bytes
  let (close, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, highPrice, lowPrice, open_, totalVolume, marketIdOfHighPrice, marketIdOfLowPrice, marketIdOfOpenPrice, numClosePrices, marketIdOfTheClose, close }, bytes)

@[simp] theorem encode_length (message : ConsolidatedStockSummaryMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ConsolidatedStockSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedStockSummaryMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConsolidatedStockSummaryMessage

/-- Consolidated Volume Message: 14 bytes -/
structure ConsolidatedVolumeMessage where
  symbolIndex : BitVec 32
  symbolSeqNumber : BitVec 32
  totalVolume : BitVec 32
  reason : BitVec 8
  complete : BitVec 8
  deriving DecidableEq, Repr

namespace ConsolidatedVolumeMessage

def encode (message : ConsolidatedVolumeMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNumber
    ++ (encodeUIntLE 4 message.totalVolume
    ++ (encodeUIntLE 1 message.reason
    ++ (encodeUIntLE 1 message.complete))))

def decode (bytes : List UInt8) : Option (ConsolidatedVolumeMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNumber, bytes) ← decodeUIntLE 4 bytes
  let (totalVolume, bytes) ← decodeUIntLE 4 bytes
  let (reason, bytes) ← decodeUIntLE 1 bytes
  let (complete, bytes) ← decodeUIntLE 1 bytes
  pure ({ symbolIndex, symbolSeqNumber, totalVolume, reason, complete }, bytes)

@[simp] theorem encode_length (message : ConsolidatedVolumeMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ConsolidatedVolumeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedVolumeMessage) (rest : List UInt8) :
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

end ConsolidatedVolumeMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | sequenceNumberResetMessage (message : SequenceNumberResetMessage) -- 1
  | symbolIndexMappingMessage (message : SymbolIndexMappingMessage) -- 3
  | retransmissionRequestMessage (message : RetransmissionRequestMessage) -- 10
  | requestResponseMessage (message : RequestResponseMessage) -- 11
  | heartbeatResponseMessage (message : HeartbeatResponseMessage) -- 12
  | symbolIndexMappingRequestMessage (message : SymbolIndexMappingRequestMessage) -- 13
  | refreshRequestMessage (message : RefreshRequestMessage) -- 15
  | messageUnavailableMessage (message : MessageUnavailableMessage) -- 31
  | consolidatedSymbolClearMessage (message : ConsolidatedSymbolClearMessage) -- 32
  | consolidatedTradingSessionChangeMessage (message : ConsolidatedTradingSessionChangeMessage) -- 33
  | consolidatedSecurityStatusMessage (message : ConsolidatedSecurityStatusMessage) -- 34
  | refreshHeaderMessage (message : RefreshHeaderMessage) -- 35
  | bqtMessage (message : BqtMessage) -- 142
  | consolidatedSingleSidedQuoteMessage (message : ConsolidatedSingleSidedQuoteMessage) -- 143
  | consolidatedTradeMessage (message : ConsolidatedTradeMessage) -- 220
  | consolidatedTradeCancelMessage (message : ConsolidatedTradeCancelMessage) -- 221
  | consolidatedTradeCorrectionMessage (message : ConsolidatedTradeCorrectionMessage) -- 222
  | consolidatedStockSummaryMessage (message : ConsolidatedStockSummaryMessage) -- 229
  | consolidatedVolumeMessage (message : ConsolidatedVolumeMessage) -- 240
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceNumberResetMessage _ => 1
  | .symbolIndexMappingMessage _ => 3
  | .retransmissionRequestMessage _ => 10
  | .requestResponseMessage _ => 11
  | .heartbeatResponseMessage _ => 12
  | .symbolIndexMappingRequestMessage _ => 13
  | .refreshRequestMessage _ => 15
  | .messageUnavailableMessage _ => 31
  | .consolidatedSymbolClearMessage _ => 32
  | .consolidatedTradingSessionChangeMessage _ => 33
  | .consolidatedSecurityStatusMessage _ => 34
  | .refreshHeaderMessage _ => 35
  | .bqtMessage _ => 142
  | .consolidatedSingleSidedQuoteMessage _ => 143
  | .consolidatedTradeMessage _ => 220
  | .consolidatedTradeCancelMessage _ => 221
  | .consolidatedTradeCorrectionMessage _ => 222
  | .consolidatedStockSummaryMessage _ => 229
  | .consolidatedVolumeMessage _ => 240

def encode : Payload → List UInt8
  | .sequenceNumberResetMessage message => SequenceNumberResetMessage.encode message
  | .symbolIndexMappingMessage message => SymbolIndexMappingMessage.encode message
  | .retransmissionRequestMessage message => RetransmissionRequestMessage.encode message
  | .requestResponseMessage message => RequestResponseMessage.encode message
  | .heartbeatResponseMessage message => HeartbeatResponseMessage.encode message
  | .symbolIndexMappingRequestMessage message => SymbolIndexMappingRequestMessage.encode message
  | .refreshRequestMessage message => RefreshRequestMessage.encode message
  | .messageUnavailableMessage message => MessageUnavailableMessage.encode message
  | .consolidatedSymbolClearMessage message => ConsolidatedSymbolClearMessage.encode message
  | .consolidatedTradingSessionChangeMessage message => ConsolidatedTradingSessionChangeMessage.encode message
  | .consolidatedSecurityStatusMessage message => ConsolidatedSecurityStatusMessage.encode message
  | .refreshHeaderMessage message => RefreshHeaderMessage.encode message
  | .bqtMessage message => BqtMessage.encode message
  | .consolidatedSingleSidedQuoteMessage message => ConsolidatedSingleSidedQuoteMessage.encode message
  | .consolidatedTradeMessage message => ConsolidatedTradeMessage.encode message
  | .consolidatedTradeCancelMessage message => ConsolidatedTradeCancelMessage.encode message
  | .consolidatedTradeCorrectionMessage message => ConsolidatedTradeCorrectionMessage.encode message
  | .consolidatedStockSummaryMessage message => ConsolidatedStockSummaryMessage.encode message
  | .consolidatedVolumeMessage message => ConsolidatedVolumeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 42 := by
  cases message with
  | sequenceNumberResetMessage inner =>
    simp only [encode, SequenceNumberResetMessage.encode_length]
    omega
  | symbolIndexMappingMessage inner =>
    simp only [encode, SymbolIndexMappingMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [encode, RetransmissionRequestMessage.encode_length]
    omega
  | requestResponseMessage inner =>
    simp only [encode, RequestResponseMessage.encode_length]
    omega
  | heartbeatResponseMessage inner =>
    simp only [encode, HeartbeatResponseMessage.encode_length]
    omega
  | symbolIndexMappingRequestMessage inner =>
    simp only [encode, SymbolIndexMappingRequestMessage.encode_length]
    omega
  | refreshRequestMessage inner =>
    simp only [encode, RefreshRequestMessage.encode_length]
    omega
  | messageUnavailableMessage inner =>
    simp only [encode, MessageUnavailableMessage.encode_length]
    omega
  | consolidatedSymbolClearMessage inner =>
    simp only [encode, ConsolidatedSymbolClearMessage.encode_length]
    omega
  | consolidatedTradingSessionChangeMessage inner =>
    simp only [encode, ConsolidatedTradingSessionChangeMessage.encode_length]
    omega
  | consolidatedSecurityStatusMessage inner =>
    simp only [encode, ConsolidatedSecurityStatusMessage.encode_length]
    omega
  | refreshHeaderMessage inner =>
    have bound_inner := RefreshHeaderMessage.encode_length_le inner
    simp only [encode]
    omega
  | bqtMessage inner =>
    simp only [encode, BqtMessage.encode_length]
    omega
  | consolidatedSingleSidedQuoteMessage inner =>
    simp only [encode, ConsolidatedSingleSidedQuoteMessage.encode_length]
    omega
  | consolidatedTradeMessage inner =>
    simp only [encode, ConsolidatedTradeMessage.encode_length]
    omega
  | consolidatedTradeCancelMessage inner =>
    simp only [encode, ConsolidatedTradeCancelMessage.encode_length]
    omega
  | consolidatedTradeCorrectionMessage inner =>
    simp only [encode, ConsolidatedTradeCorrectionMessage.encode_length]
    omega
  | consolidatedStockSummaryMessage inner =>
    simp only [encode, ConsolidatedStockSummaryMessage.encode_length]
    omega
  | consolidatedVolumeMessage inner =>
    simp only [encode, ConsolidatedVolumeMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (SequenceNumberResetMessage.decode bytes).map fun (message, rest) => (.sequenceNumberResetMessage message, rest)
  else if tag = 3 then (SymbolIndexMappingMessage.decode bytes).map fun (message, rest) => (.symbolIndexMappingMessage message, rest)
  else if tag = 10 then (RetransmissionRequestMessage.decode bytes).map fun (message, rest) => (.retransmissionRequestMessage message, rest)
  else if tag = 11 then (RequestResponseMessage.decode bytes).map fun (message, rest) => (.requestResponseMessage message, rest)
  else if tag = 12 then (HeartbeatResponseMessage.decode bytes).map fun (message, rest) => (.heartbeatResponseMessage message, rest)
  else if tag = 13 then (SymbolIndexMappingRequestMessage.decode bytes).map fun (message, rest) => (.symbolIndexMappingRequestMessage message, rest)
  else if tag = 15 then (RefreshRequestMessage.decode bytes).map fun (message, rest) => (.refreshRequestMessage message, rest)
  else if tag = 31 then (MessageUnavailableMessage.decode bytes).map fun (message, rest) => (.messageUnavailableMessage message, rest)
  else if tag = 32 then (ConsolidatedSymbolClearMessage.decode bytes).map fun (message, rest) => (.consolidatedSymbolClearMessage message, rest)
  else if tag = 33 then (ConsolidatedTradingSessionChangeMessage.decode bytes).map fun (message, rest) => (.consolidatedTradingSessionChangeMessage message, rest)
  else if tag = 34 then (ConsolidatedSecurityStatusMessage.decode bytes).map fun (message, rest) => (.consolidatedSecurityStatusMessage message, rest)
  else if tag = 35 then (RefreshHeaderMessage.decode bytes).map fun (message, rest) => (.refreshHeaderMessage message, rest)
  else if tag = 142 then (BqtMessage.decode bytes).map fun (message, rest) => (.bqtMessage message, rest)
  else if tag = 143 then (ConsolidatedSingleSidedQuoteMessage.decode bytes).map fun (message, rest) => (.consolidatedSingleSidedQuoteMessage message, rest)
  else if tag = 220 then (ConsolidatedTradeMessage.decode bytes).map fun (message, rest) => (.consolidatedTradeMessage message, rest)
  else if tag = 221 then (ConsolidatedTradeCancelMessage.decode bytes).map fun (message, rest) => (.consolidatedTradeCancelMessage message, rest)
  else if tag = 222 then (ConsolidatedTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.consolidatedTradeCorrectionMessage message, rest)
  else if tag = 229 then (ConsolidatedStockSummaryMessage.decode bytes).map fun (message, rest) => (.consolidatedStockSummaryMessage message, rest)
  else if tag = 240 then (ConsolidatedVolumeMessage.decode bytes).map fun (message, rest) => (.consolidatedVolumeMessage message, rest)
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
  | sequenceNumberResetMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SequenceNumberResetMessage.encode_length]
    omega
  | symbolIndexMappingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SymbolIndexMappingMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RetransmissionRequestMessage.encode_length]
    omega
  | requestResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RequestResponseMessage.encode_length]
    omega
  | heartbeatResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, HeartbeatResponseMessage.encode_length]
    omega
  | symbolIndexMappingRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SymbolIndexMappingRequestMessage.encode_length]
    omega
  | refreshRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RefreshRequestMessage.encode_length]
    omega
  | messageUnavailableMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, MessageUnavailableMessage.encode_length]
    omega
  | consolidatedSymbolClearMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedSymbolClearMessage.encode_length]
    omega
  | consolidatedTradingSessionChangeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedTradingSessionChangeMessage.encode_length]
    omega
  | consolidatedSecurityStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedSecurityStatusMessage.encode_length]
    omega
  | refreshHeaderMessage inner =>
    have bound_inner := RefreshHeaderMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | bqtMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, BqtMessage.encode_length]
    omega
  | consolidatedSingleSidedQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedSingleSidedQuoteMessage.encode_length]
    omega
  | consolidatedTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedTradeMessage.encode_length]
    omega
  | consolidatedTradeCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedTradeCancelMessage.encode_length]
    omega
  | consolidatedTradeCorrectionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedTradeCorrectionMessage.encode_length]
    omega
  | consolidatedStockSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedStockSummaryMessage.encode_length]
    omega
  | consolidatedVolumeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ConsolidatedVolumeMessage.encode_length]
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

end Omi.NyseNyseequitiesBqtXdpV17A
