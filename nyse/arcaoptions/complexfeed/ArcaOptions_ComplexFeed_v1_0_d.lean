import Wire

/-!
# New York Stock Exchange Complex Feed v1.0.d

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseArcaoptionsComplexfeedPillarV10D

/-- Exchange Code: one byte code -/
def ExchangeCode.codes : List UInt8 :=
  [0x41, 0x4C, 0x4E, 0x50, 0x51, 0x56, 0x5A, 0x20]

inductive ExchangeCode where
  | nyseAmerican -- Nyse American
  | ltse -- Ltse
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | iex -- Iex
  | cboe -- Cboe
  | otcOrIndexedProduct -- Otc Or Indexed Product
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeCode

def toByte : ExchangeCode → UInt8
  | .nyseAmerican => 0x41
  | .ltse => 0x4C
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .iex => 0x56
  | .cboe => 0x5A
  | .otcOrIndexedProduct => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExchangeCode :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x4C then .ltse
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x56 then .iex
  else if byte = 0x5A then .cboe
  else .otcOrIndexedProduct

def ofByte (byte : UInt8) : ExchangeCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeCode) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | ltse => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | iex => decide
  | cboe => decide
  | otcOrIndexedProduct => decide
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
  | closedEndFund -- Closed End Fund
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
  | .closedEndFund => 0x55
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
  else if byte = 0x55 then .closedEndFund
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
  | closedEndFund => decide
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
  | accepted -- Accepted
  | rejected -- Rejected
  | invalidSequenceRange -- Invalid Sequence Range
  | maximumSequenceRange -- Maximum Sequence Range
  | maximumRequestInADay -- Maximum Request In A Day
  | maximumRefreshRequestsInADay -- Maximum Refresh Requests In A Day
  | oldSeqNumTtl -- Old Seq Num Ttl
  | invalidChannelId -- Invalid Channel Id
  | invalidProductId -- Invalid Product Id
  | invalidMsgTypeOrMsgSize -- Invalid Msg Type Or Msg Size
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .accepted => 0x30
  | .rejected => 0x31
  | .invalidSequenceRange => 0x32
  | .maximumSequenceRange => 0x33
  | .maximumRequestInADay => 0x34
  | .maximumRefreshRequestsInADay => 0x35
  | .oldSeqNumTtl => 0x36
  | .invalidChannelId => 0x37
  | .invalidProductId => 0x38
  | .invalidMsgTypeOrMsgSize => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x30 then .accepted
  else if byte = 0x31 then .rejected
  else if byte = 0x32 then .invalidSequenceRange
  else if byte = 0x33 then .maximumSequenceRange
  else if byte = 0x34 then .maximumRequestInADay
  else if byte = 0x35 then .maximumRefreshRequestsInADay
  else if byte = 0x36 then .oldSeqNumTtl
  else if byte = 0x37 then .invalidChannelId
  else if byte = 0x38 then .invalidProductId
  else .invalidMsgTypeOrMsgSize

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | accepted => decide
  | rejected => decide
  | invalidSequenceRange => decide
  | maximumSequenceRange => decide
  | maximumRequestInADay => decide
  | maximumRefreshRequestsInADay => decide
  | oldSeqNumTtl => decide
  | invalidChannelId => decide
  | invalidProductId => decide
  | invalidMsgTypeOrMsgSize => decide
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
  [0x34, 0x35, 0x36, 0x41, 0x43, 0x44, 0x50, 0x42, 0x45, 0x4F, 0x4C, 0x58, 0x49, 0x47]

inductive SecurityStatus where
  | tradingHalt -- Trading Halt
  | resume -- Resume
  | suspend -- Suspend
  | shortSaleRestrictionActivatedDay1 -- Short Sale Restriction Activated Day 1
  | shortSaleRestrictionContinuedDay2 -- Short Sale Restriction Continued Day 2
  | shortSaleRestrictionDeactivated -- Short Sale Restriction Deactivated
  | preopening -- Preopening
  | beginAcceptingOrders -- Begin Accepting Orders
  | earlySession -- Early Session
  | coreSession -- Core Session
  | lateSession -- Late Session
  | closed -- Closed
  | haltResumePriceIndication -- Halt Resume Price Indication
  | preOpeningPriceIndication -- Pre Opening Price Indication
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatus

def toByte : SecurityStatus → UInt8
  | .tradingHalt => 0x34
  | .resume => 0x35
  | .suspend => 0x36
  | .shortSaleRestrictionActivatedDay1 => 0x41
  | .shortSaleRestrictionContinuedDay2 => 0x43
  | .shortSaleRestrictionDeactivated => 0x44
  | .preopening => 0x50
  | .beginAcceptingOrders => 0x42
  | .earlySession => 0x45
  | .coreSession => 0x4F
  | .lateSession => 0x4C
  | .closed => 0x58
  | .haltResumePriceIndication => 0x49
  | .preOpeningPriceIndication => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x34 then .tradingHalt
  else if byte = 0x35 then .resume
  else if byte = 0x36 then .suspend
  else if byte = 0x41 then .shortSaleRestrictionActivatedDay1
  else if byte = 0x43 then .shortSaleRestrictionContinuedDay2
  else if byte = 0x44 then .shortSaleRestrictionDeactivated
  else if byte = 0x50 then .preopening
  else if byte = 0x42 then .beginAcceptingOrders
  else if byte = 0x45 then .earlySession
  else if byte = 0x4F then .coreSession
  else if byte = 0x4C then .lateSession
  else if byte = 0x58 then .closed
  else if byte = 0x49 then .haltResumePriceIndication
  else .preOpeningPriceIndication

def ofByte (byte : UInt8) : SecurityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatus) : ofByte value.toByte = value := by
  cases value with
  | tradingHalt => decide
  | resume => decide
  | suspend => decide
  | shortSaleRestrictionActivatedDay1 => decide
  | shortSaleRestrictionContinuedDay2 => decide
  | shortSaleRestrictionDeactivated => decide
  | preopening => decide
  | beginAcceptingOrders => decide
  | earlySession => decide
  | coreSession => decide
  | lateSession => decide
  | closed => decide
  | haltResumePriceIndication => decide
  | preOpeningPriceIndication => decide
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
  [0x7E, 0x44, 0x49, 0x50, 0x4D, 0x58, 0x41, 0x43, 0x45, 0x46, 0x4E, 0x4F, 0x56, 0x31, 0x32, 0x33]

inductive HaltCondition where
  | securityNotDelayedOrHalted -- Security Not Delayed Or Halted
  | newsReleased -- News Released
  | orderImbalance -- Order Imbalance
  | newsPending -- News Pending
  | luldPause -- Luld Pause
  | equipmentChangeover -- Equipment Changeover
  | additionalInformationRequested -- Additional Information Requested
  | regulatoryConcern -- Regulatory Concern
  | mergerEffective -- Merger Effective
  | etfComponentPricesNotAvailable -- Etf Component Prices Not Available
  | corporateAction -- Corporate Action
  | newSecurityOffering -- New Security Offering
  | intradayIndicativeValueNotAvailable -- Intraday Indicative Value Not Available
  | marketWideCircuitBreakerHaltLevel1 -- Market Wide Circuit Breaker Halt Level 1
  | marketWideCircuitBreakerHaltLevel2 -- Market Wide Circuit Breaker Halt Level 2
  | marketWideCircuitBreakerHaltLevel3 -- Market Wide Circuit Breaker Halt Level 3
  | unlisted (byte : { byte : UInt8 // byte ∉ HaltCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HaltCondition

def toByte : HaltCondition → UInt8
  | .securityNotDelayedOrHalted => 0x7E
  | .newsReleased => 0x44
  | .orderImbalance => 0x49
  | .newsPending => 0x50
  | .luldPause => 0x4D
  | .equipmentChangeover => 0x58
  | .additionalInformationRequested => 0x41
  | .regulatoryConcern => 0x43
  | .mergerEffective => 0x45
  | .etfComponentPricesNotAvailable => 0x46
  | .corporateAction => 0x4E
  | .newSecurityOffering => 0x4F
  | .intradayIndicativeValueNotAvailable => 0x56
  | .marketWideCircuitBreakerHaltLevel1 => 0x31
  | .marketWideCircuitBreakerHaltLevel2 => 0x32
  | .marketWideCircuitBreakerHaltLevel3 => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HaltCondition :=
  if byte = 0x7E then .securityNotDelayedOrHalted
  else if byte = 0x44 then .newsReleased
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x50 then .newsPending
  else if byte = 0x4D then .luldPause
  else if byte = 0x58 then .equipmentChangeover
  else if byte = 0x41 then .additionalInformationRequested
  else if byte = 0x43 then .regulatoryConcern
  else if byte = 0x45 then .mergerEffective
  else if byte = 0x46 then .etfComponentPricesNotAvailable
  else if byte = 0x4E then .corporateAction
  else if byte = 0x4F then .newSecurityOffering
  else if byte = 0x56 then .intradayIndicativeValueNotAvailable
  else if byte = 0x31 then .marketWideCircuitBreakerHaltLevel1
  else if byte = 0x32 then .marketWideCircuitBreakerHaltLevel2
  else .marketWideCircuitBreakerHaltLevel3

def ofByte (byte : UInt8) : HaltCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HaltCondition) : ofByte value.toByte = value := by
  cases value with
  | securityNotDelayedOrHalted => decide
  | newsReleased => decide
  | orderImbalance => decide
  | newsPending => decide
  | luldPause => decide
  | equipmentChangeover => decide
  | additionalInformationRequested => decide
  | regulatoryConcern => decide
  | mergerEffective => decide
  | etfComponentPricesNotAvailable => decide
  | corporateAction => decide
  | newSecurityOffering => decide
  | intradayIndicativeValueNotAvailable => decide
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
  [0x41, 0x42, 0x43, 0x44, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x53, 0x54, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x48, 0x55, 0x20]

inductive SsrTriggeringExchangeId where
  | nyseAmerican -- Nyse American
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nyseNational -- Nyse National
  | finra -- Finra
  | ise -- Ise
  | edga -- Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseChicago -- Nyse Chicago
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | cts -- Cts
  | nasdaqOmx -- Nasdaq Omx
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqOmxPsx -- Nasdaq Omx Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | miax -- Miax
  | memx -- Memx
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
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseChicago => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .cts => 0x53
  | .nasdaqOmx => 0x54
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqOmxPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .miax => 0x48
  | .memx => 0x55
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
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x53 then .cts
  else if byte = 0x54 then .nasdaqOmx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqOmxPsx
  else if byte = 0x59 then .cboeByx
  else if byte = 0x5A then .cboeBzx
  else if byte = 0x48 then .miax
  else if byte = 0x55 then .memx
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
  | cboeEdgx => decide
  | ltse => decide
  | nyseChicago => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | cts => decide
  | nasdaqOmx => decide
  | iex => decide
  | cbsx => decide
  | nasdaqOmxPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | miax => decide
  | memx => decide
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

/-- Closing Only Indicator: one byte code -/
def ClosingOnlyIndicator.codes : List UInt8 :=
  [0x30, 0x31]

inductive ClosingOnlyIndicator where
  | standardSeries -- Standard Series
  | call -- Call
  | unlisted (byte : { byte : UInt8 // byte ∉ ClosingOnlyIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClosingOnlyIndicator

def toByte : ClosingOnlyIndicator → UInt8
  | .standardSeries => 0x30
  | .call => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClosingOnlyIndicator :=
  if byte = 0x30 then .standardSeries
  else .call

def ofByte (byte : UInt8) : ClosingOnlyIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClosingOnlyIndicator) : ofByte value.toByte = value := by
  cases value with
  | standardSeries => decide
  | call => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClosingOnlyIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClosingOnlyIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClosingOnlyIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ClosingOnlyIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClosingOnlyIndicator

/-- Series Status: one byte code -/
def SeriesStatus.codes : List UInt8 :=
  [0x34, 0x35, 0x36, 0x50, 0x42, 0x4F, 0x58]

inductive SeriesStatus where
  | tradingHalt -- Trading Halt
  | resume -- Resume
  | suspend -- Suspend
  | preopening -- Preopening
  | beginAcceptingOrders -- Begin Accepting Orders
  | coreSession -- Core Session
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ SeriesStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SeriesStatus

def toByte : SeriesStatus → UInt8
  | .tradingHalt => 0x34
  | .resume => 0x35
  | .suspend => 0x36
  | .preopening => 0x50
  | .beginAcceptingOrders => 0x42
  | .coreSession => 0x4F
  | .closed => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SeriesStatus :=
  if byte = 0x34 then .tradingHalt
  else if byte = 0x35 then .resume
  else if byte = 0x36 then .suspend
  else if byte = 0x50 then .preopening
  else if byte = 0x42 then .beginAcceptingOrders
  else if byte = 0x4F then .coreSession
  else .closed

def ofByte (byte : UInt8) : SeriesStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SeriesStatus) : ofByte value.toByte = value := by
  cases value with
  | tradingHalt => decide
  | resume => decide
  | suspend => decide
  | preopening => decide
  | beginAcceptingOrders => decide
  | coreSession => decide
  | closed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SeriesStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SeriesStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SeriesStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SeriesStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SeriesStatus

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
  [0x31, 0x32, 0x33]

inductive QuoteCondition where
  | regularTrading -- Regular Trading
  | rotation -- Rotation
  | tradingHalted -- Trading Halted
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .regularTrading => 0x31
  | .rotation => 0x32
  | .tradingHalted => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x31 then .regularTrading
  else if byte = 0x32 then .rotation
  else .tradingHalted

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | regularTrading => decide
  | rotation => decide
  | tradingHalted => decide
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

/-- Series: one byte code -/
def Series.codes : List UInt8 :=
  [0x61, 0x63, 0x65, 0x49, 0x53, 0x44, 0x66, 0x67, 0x48, 0x69, 0x6A, 0x6D, 0x70, 0x73]

inductive Series where
  | cube -- Cube
  | occ -- Occ
  | floorTrade -- Floor Trade
  | otherOutrightSeries -- Other Outright Series
  | isoSweep -- Iso Sweep
  | after90Seconds -- After 90 Seconds
  | otherComplexOrders -- Other Complex Orders
  | complexCube -- Complex Cube
  | complexQccOrder -- Complex Qcc Order
  | complexFloorOrder -- Complex Floor Order
  | complexOrderTradingWithTheOutrightSeries -- Complex Order Trading With The Outright Series
  | complexOrderToOutrightSeriesOrderfloorTrade -- Complex Order To Outright Series Orderfloor Trade
  | complexOrderWithStockToComplexOrderWithStockFloorTrade -- Complex Order With Stock To Complex Order With Stock Floor Trade
  | complexOrderWithStockToOutrightSeriesOrderFloorTrade -- Complex Order With Stock To Outright Series Order Floor Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ Series.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Series

def toByte : Series → UInt8
  | .cube => 0x61
  | .occ => 0x63
  | .floorTrade => 0x65
  | .otherOutrightSeries => 0x49
  | .isoSweep => 0x53
  | .after90Seconds => 0x44
  | .otherComplexOrders => 0x66
  | .complexCube => 0x67
  | .complexQccOrder => 0x48
  | .complexFloorOrder => 0x69
  | .complexOrderTradingWithTheOutrightSeries => 0x6A
  | .complexOrderToOutrightSeriesOrderfloorTrade => 0x6D
  | .complexOrderWithStockToComplexOrderWithStockFloorTrade => 0x70
  | .complexOrderWithStockToOutrightSeriesOrderFloorTrade => 0x73
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Series :=
  if byte = 0x61 then .cube
  else if byte = 0x63 then .occ
  else if byte = 0x65 then .floorTrade
  else if byte = 0x49 then .otherOutrightSeries
  else if byte = 0x53 then .isoSweep
  else if byte = 0x44 then .after90Seconds
  else if byte = 0x66 then .otherComplexOrders
  else if byte = 0x67 then .complexCube
  else if byte = 0x48 then .complexQccOrder
  else if byte = 0x69 then .complexFloorOrder
  else if byte = 0x6A then .complexOrderTradingWithTheOutrightSeries
  else if byte = 0x6D then .complexOrderToOutrightSeriesOrderfloorTrade
  else if byte = 0x70 then .complexOrderWithStockToComplexOrderWithStockFloorTrade
  else .complexOrderWithStockToOutrightSeriesOrderFloorTrade

def ofByte (byte : UInt8) : Series :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Series) : ofByte value.toByte = value := by
  cases value with
  | cube => decide
  | occ => decide
  | floorTrade => decide
  | otherOutrightSeries => decide
  | isoSweep => decide
  | after90Seconds => decide
  | otherComplexOrders => decide
  | complexCube => decide
  | complexQccOrder => decide
  | complexFloorOrder => decide
  | complexOrderTradingWithTheOutrightSeries => decide
  | complexOrderToOutrightSeriesOrderfloorTrade => decide
  | complexOrderWithStockToComplexOrderWithStockFloorTrade => decide
  | complexOrderWithStockToOutrightSeriesOrderFloorTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Series) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Series × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Series) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Series) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Series

/-- Type: one byte code -/
def Type_.codes : List UInt8 :=
  [0x50, 0x46, 0x53, 0x42, 0x43]

inductive Type_ where
  | priceImprovement -- Price Improvement
  | facilitation -- Facilitation
  | solicitation -- Solicitation
  | bold -- Bold
  | coa -- Coa
  | unlisted (byte : { byte : UInt8 // byte ∉ Type_.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Type_

def toByte : Type_ → UInt8
  | .priceImprovement => 0x50
  | .facilitation => 0x46
  | .solicitation => 0x53
  | .bold => 0x42
  | .coa => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Type_ :=
  if byte = 0x50 then .priceImprovement
  else if byte = 0x46 then .facilitation
  else if byte = 0x53 then .solicitation
  else if byte = 0x42 then .bold
  else .coa

def ofByte (byte : UInt8) : Type_ :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Type_) : ofByte value.toByte = value := by
  cases value with
  | priceImprovement => decide
  | facilitation => decide
  | solicitation => decide
  | bold => decide
  | coa => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Type_) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Type_ × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Type_) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Type_) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Type_

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x20, 0x30, 0x31, 0x32, 0x33, 0x38]

inductive Capacity where
  | notSpecified -- Not Specified
  | customer -- Customer
  | firm -- Firm
  | brokerDealer -- Broker Dealer
  | marketMaker -- Market Maker
  | professionalCustomer -- Professional Customer
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .notSpecified => 0x20
  | .customer => 0x30
  | .firm => 0x31
  | .brokerDealer => 0x32
  | .marketMaker => 0x33
  | .professionalCustomer => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x20 then .notSpecified
  else if byte = 0x30 then .customer
  else if byte = 0x31 then .firm
  else if byte = 0x32 then .brokerDealer
  else if byte = 0x33 then .marketMaker
  else .professionalCustomer

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | notSpecified => decide
  | customer => decide
  | firm => decide
  | brokerDealer => decide
  | marketMaker => decide
  | professionalCustomer => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Capacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Capacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Capacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Capacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Capacity

/-- Rfq Status: one byte code -/
def RfqStatus.codes : List UInt8 :=
  [0x4F, 0x51]

inductive RfqStatus where
  | start -- Start
  | end_ -- End
  | unlisted (byte : { byte : UInt8 // byte ∉ RfqStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RfqStatus

def toByte : RfqStatus → UInt8
  | .start => 0x4F
  | .end_ => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RfqStatus :=
  if byte = 0x4F then .start
  else .end_

def ofByte (byte : UInt8) : RfqStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RfqStatus) : ofByte value.toByte = value := by
  cases value with
  | start => decide
  | end_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RfqStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RfqStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RfqStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RfqStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RfqStatus

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

/-- Time Reference Message: 12 bytes -/
structure TimeReferenceMessage where
  id : BitVec 32
  reserved4 : Alpha 4
  sourceTime : BitVec 32
  deriving DecidableEq, Repr

namespace TimeReferenceMessage

def encode (message : TimeReferenceMessage) : List UInt8 :=
  encodeUIntLE 4 message.id
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 4 message.sourceTime))

def decode (bytes : List UInt8) : Option (TimeReferenceMessage × List UInt8) := do
  let (id, bytes) ← decodeUIntLE 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  pure ({ id, reserved4, sourceTime }, bytes)

@[simp] theorem encode_length (message : TimeReferenceMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TimeReferenceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimeReferenceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TimeReferenceMessage

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
  reserved6 : Alpha 6
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
    ++ (Alpha.encode message.reserved6)))))))))))))

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
  let (reserved6, bytes) ← Alpha.decode 6 bytes
  pure ({ symbolIndex, symbol, reserved1, marketId, systemId, exchangeCode, priceScaleCode, securityType, lotSize, prevClosePrice, prevCloseVolume, priceResolution, roundLot, reserved6 }, bytes)

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

/-- Symbol Clear Message: 16 bytes -/
structure SymbolClearMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  nextSourceSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace SymbolClearMessage

def encode (message : SymbolClearMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.nextSourceSeqNum)))

def decode (bytes : List UInt8) : Option (SymbolClearMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (nextSourceSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, nextSourceSeqNum }, bytes)

@[simp] theorem encode_length (message : SymbolClearMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SymbolClearMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolClearMessage) (rest : List UInt8) :
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

end SymbolClearMessage

/-- Security Status Message: 42 bytes -/
structure SecurityStatusMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  securityStatus : SecurityStatus
  haltCondition : HaltCondition
  reserved4 : Alpha 4
  price1 : BitVec 32
  price2 : BitVec 32
  ssrTriggeringExchangeId : SsrTriggeringExchangeId
  ssrTriggeringVolume : BitVec 32
  time : BitVec 32
  ssrState : SsrState
  marketState : MarketState
  sessionState : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (SecurityStatus.encode message.securityStatus
    ++ (HaltCondition.encode message.haltCondition
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 4 message.price1
    ++ (encodeUIntLE 4 message.price2
    ++ (SsrTriggeringExchangeId.encode message.ssrTriggeringExchangeId
    ++ (encodeUIntLE 4 message.ssrTriggeringVolume
    ++ (encodeUIntLE 4 message.time
    ++ (SsrState.encode message.ssrState
    ++ (MarketState.encode message.marketState
    ++ (encodeUIntLE 1 message.sessionState))))))))))))))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (haltCondition, bytes) ← HaltCondition.decode bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (price1, bytes) ← decodeUIntLE 4 bytes
  let (price2, bytes) ← decodeUIntLE 4 bytes
  let (ssrTriggeringExchangeId, bytes) ← SsrTriggeringExchangeId.decode bytes
  let (ssrTriggeringVolume, bytes) ← decodeUIntLE 4 bytes
  let (time, bytes) ← decodeUIntLE 4 bytes
  let (ssrState, bytes) ← SsrState.decode bytes
  let (marketState, bytes) ← MarketState.decode bytes
  let (sessionState, bytes) ← decodeUIntLE 1 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, securityStatus, haltCondition, reserved4, price1, price2, ssrTriggeringExchangeId, ssrTriggeringVolume, time, ssrState, marketState, sessionState }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityStatus.encode_length, HaltCondition.encode_length, Alpha.encode_length, SsrTriggeringExchangeId.encode_length, SsrState.encode_length, MarketState.encode_length]

theorem encode_length_pos (message : SecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityStatusMessage

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

/-- Outright Series Index Mapping Message: 51 bytes -/
structure OutrightSeriesIndexMappingMessage where
  seriesIndex : BitVec 32
  seriesType : BitVec 8
  marketId : BitVec 16
  systemId : BitVec 8
  optionSymbolRoot : Alpha 6
  underlyingSymbol : Alpha 11
  underlyingIndex : BitVec 32
  priceScaleCode : BitVec 8
  contractMultiplier : BitVec 16
  maturityDate : Alpha 6
  putOrCall : BitVec 8
  strikePrice : Alpha 10
  closingOnlyIndicator : ClosingOnlyIndicator
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace OutrightSeriesIndexMappingMessage

def encode (message : OutrightSeriesIndexMappingMessage) : List UInt8 :=
  encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 1 message.seriesType
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUIntLE 1 message.systemId
    ++ (Alpha.encode message.optionSymbolRoot
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.underlyingIndex
    ++ (encodeUIntLE 1 message.priceScaleCode
    ++ (encodeUIntLE 2 message.contractMultiplier
    ++ (Alpha.encode message.maturityDate
    ++ (encodeUIntLE 1 message.putOrCall
    ++ (Alpha.encode message.strikePrice
    ++ (ClosingOnlyIndicator.encode message.closingOnlyIndicator
    ++ (Alpha.encode message.reserved1)))))))))))))

def decode (bytes : List UInt8) : Option (OutrightSeriesIndexMappingMessage × List UInt8) := do
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesType, bytes) ← decodeUIntLE 1 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (systemId, bytes) ← decodeUIntLE 1 bytes
  let (optionSymbolRoot, bytes) ← Alpha.decode 6 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (underlyingIndex, bytes) ← decodeUIntLE 4 bytes
  let (priceScaleCode, bytes) ← decodeUIntLE 1 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (maturityDate, bytes) ← Alpha.decode 6 bytes
  let (putOrCall, bytes) ← decodeUIntLE 1 bytes
  let (strikePrice, bytes) ← Alpha.decode 10 bytes
  let (closingOnlyIndicator, bytes) ← ClosingOnlyIndicator.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ seriesIndex, seriesType, marketId, systemId, optionSymbolRoot, underlyingSymbol, underlyingIndex, priceScaleCode, contractMultiplier, maturityDate, putOrCall, strikePrice, closingOnlyIndicator, reserved1 }, bytes)

@[simp] theorem encode_length (message : OutrightSeriesIndexMappingMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ClosingOnlyIndicator.encode_length]

theorem encode_length_pos (message : OutrightSeriesIndexMappingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightSeriesIndexMappingMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClosingOnlyIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutrightSeriesIndexMappingMessage

/-- Options Status Message: 19 bytes -/
structure OptionsStatusMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  seriesStatus : SeriesStatus
  marketState : MarketState
  haltCondition : HaltCondition
  deriving DecidableEq, Repr

namespace OptionsStatusMessage

def encode (message : OptionsStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (MarketState.encode message.marketState
    ++ (HaltCondition.encode message.haltCondition))))))

def decode (bytes : List UInt8) : Option (OptionsStatusMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (marketState, bytes) ← MarketState.decode bytes
  let (haltCondition, bytes) ← HaltCondition.decode bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, seriesSeqNum, seriesStatus, marketState, haltCondition }, bytes)

@[simp] theorem encode_length (message : OptionsStatusMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SeriesStatus.encode_length, MarketState.encode_length, HaltCondition.encode_length]

theorem encode_length_pos (message : OptionsStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsStatusMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketState.decode_encode, some_bind]
  dsimp only
  rw [HaltCondition.decode_encode, some_bind]
  rfl

end OptionsStatusMessage

/-- Leg Definition: 8 bytes -/
structure LegDefinition where
  symbolIndex : BitVec 32
  legRatioQty : BitVec 16
  side : Side
  legSecurityType : Alpha 1
  deriving DecidableEq, Repr

namespace LegDefinition

def encode (message : LegDefinition) : List UInt8 :=
  encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 2 message.legRatioQty
    ++ (Side.encode message.side
    ++ (Alpha.encode message.legSecurityType)))

def decode (bytes : List UInt8) : Option (LegDefinition × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← Side.decode bytes
  let (legSecurityType, bytes) ← Alpha.decode 1 bytes
  pure ({ symbolIndex, legRatioQty, side, legSecurityType }, bytes)

@[simp] theorem encode_length (message : LegDefinition) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

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
  rw [Alpha.decode_encode, some_bind]
  rfl

end LegDefinition

/-- Complex Series Index Mapping Message -/
structure ComplexSeriesIndexMappingMessage where
  seriesIndex : BitVec 32
  marketId : BitVec 16
  systemId : BitVec 8
  legDefinition : Bounded 2 LegDefinition
  deriving DecidableEq, Repr

namespace ComplexSeriesIndexMappingMessage

def encode (message : ComplexSeriesIndexMappingMessage) : List UInt8 :=
  encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUIntLE 1 message.systemId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.legDefinition.val.length)
    ++ (encodeMany LegDefinition.encode message.legDefinition.val))))

def decode (bytes : List UInt8) : Option (ComplexSeriesIndexMappingMessage × List UInt8) := do
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (systemId, bytes) ← decodeUIntLE 1 bytes
  let (noOfLegs, bytes) ← decodeUIntLE 2 bytes
  let (legDefinition_, bytes) ← decodeMany LegDefinition.decode noOfLegs.toNat bytes
  if fits_legDefinition : legDefinition_.length < 256 ^ 2 then
    pure ({ seriesIndex, marketId, systemId, legDefinition := ⟨legDefinition_, fits_legDefinition⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexSeriesIndexMappingMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexSeriesIndexMappingMessage) : (encode message).length ≤ 524289 := by
  have bound_legDefinition := message.legDefinition.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const LegDefinition.encode 8 LegDefinition.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexSeriesIndexMappingMessage) (rest : List UInt8) :
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
  rw [decodeMany_bounded 2 LegDefinition.encode LegDefinition.decode LegDefinition.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legDefinition.length_lt]
  rfl

end ComplexSeriesIndexMappingMessage

/-- Options Quote Message: 38 bytes -/
structure OptionsQuoteMessage where
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  askPrice : BitVec 32
  askVolume : BitVec 32
  bidPrice : BitVec 32
  bidVolume : BitVec 32
  quoteCondition : QuoteCondition
  reserved1 : Alpha 1
  askCustomerVolume : BitVec 32
  bidCustomerVolume : BitVec 32
  deriving DecidableEq, Repr

namespace OptionsQuoteMessage

def encode (message : OptionsQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (encodeUIntLE 4 message.askPrice
    ++ (encodeUIntLE 4 message.askVolume
    ++ (encodeUIntLE 4 message.bidPrice
    ++ (encodeUIntLE 4 message.bidVolume
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 4 message.askCustomerVolume
    ++ (encodeUIntLE 4 message.bidCustomerVolume))))))))))

def decode (bytes : List UInt8) : Option (OptionsQuoteMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (askPrice, bytes) ← decodeUIntLE 4 bytes
  let (askVolume, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 4 bytes
  let (bidVolume, bytes) ← decodeUIntLE 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (askCustomerVolume, bytes) ← decodeUIntLE 4 bytes
  let (bidCustomerVolume, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceTimeNs, seriesIndex, seriesSeqNum, askPrice, askVolume, bidPrice, bidVolume, quoteCondition, reserved1, askCustomerVolume, bidCustomerVolume }, bytes)

@[simp] theorem encode_length (message : OptionsQuoteMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, QuoteCondition.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OptionsQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsQuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OptionsQuoteMessage

/-- Trade Condition: 4 bytes -/
structure TradeCondition where
  series : Series
  reserved3 : Alpha 3
  deriving DecidableEq, Repr

namespace TradeCondition

def encode (message : TradeCondition) : List UInt8 :=
  Series.encode message.series
    ++ (Alpha.encode message.reserved3)

def decode (bytes : List UInt8) : Option (TradeCondition × List UInt8) := do
  let (series, bytes) ← Series.decode bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  pure ({ series, reserved3 }, bytes)

@[simp] theorem encode_length (message : TradeCondition) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, Series.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeCondition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCondition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Series.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCondition

/-- Options Trade Message: 32 bytes -/
structure OptionsTradeMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  tradeCondition : TradeCondition
  deriving DecidableEq, Repr

namespace OptionsTradeMessage

def encode (message : OptionsTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (TradeCondition.encode message.tradeCondition)))))))

def decode (bytes : List UInt8) : Option (OptionsTradeMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (tradeCondition, bytes) ← TradeCondition.decode bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, seriesSeqNum, tradeId, price, volume, tradeCondition }, bytes)

@[simp] theorem encode_length (message : OptionsTradeMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeCondition.encode_length]

theorem encode_length_pos (message : OptionsTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsTradeMessage) (rest : List UInt8) :
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
  rw [TradeCondition.decode_encode, some_bind]
  rfl

end OptionsTradeMessage

/-- Series Rfq Message: 40 bytes -/
structure SeriesRfqMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  seriesSeqNum : BitVec 32
  side : Side
  type : Type_
  capacity : Capacity
  totalQuantity : BitVec 32
  workingPrice : BitVec 32
  participant : BitVec 32
  auctionId : BitVec 64
  rfqStatus : RfqStatus
  deriving DecidableEq, Repr

namespace SeriesRfqMessage

def encode (message : SeriesRfqMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.seriesSeqNum
    ++ (Side.encode message.side
    ++ (Type_.encode message.type
    ++ (Capacity.encode message.capacity
    ++ (encodeUIntLE 4 message.totalQuantity
    ++ (encodeUIntLE 4 message.workingPrice
    ++ (encodeUIntLE 4 message.participant
    ++ (encodeUIntLE 8 message.auctionId
    ++ (RfqStatus.encode message.rfqStatus)))))))))))

def decode (bytes : List UInt8) : Option (SeriesRfqMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (seriesSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (type, bytes) ← Type_.decode bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (totalQuantity, bytes) ← decodeUIntLE 4 bytes
  let (workingPrice, bytes) ← decodeUIntLE 4 bytes
  let (participant, bytes) ← decodeUIntLE 4 bytes
  let (auctionId, bytes) ← decodeUIntLE 8 bytes
  let (rfqStatus, bytes) ← RfqStatus.decode bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, seriesSeqNum, side, type, capacity, totalQuantity, workingPrice, participant, auctionId, rfqStatus }, bytes)

@[simp] theorem encode_length (message : SeriesRfqMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Type_.encode_length, Capacity.encode_length, RfqStatus.encode_length]

theorem encode_length_pos (message : SeriesRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesRfqMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Type_.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [RfqStatus.decode_encode, some_bind]
  rfl

end SeriesRfqMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | sequenceNumberResetMessage (message : SequenceNumberResetMessage) -- 1
  | timeReferenceMessage (message : TimeReferenceMessage) -- 2
  | symbolIndexMappingMessage (message : SymbolIndexMappingMessage) -- 3
  | retransmissionRequestMessage (message : RetransmissionRequestMessage) -- 10
  | requestResponseMessage (message : RequestResponseMessage) -- 11
  | heartbeatResponseMessage (message : HeartbeatResponseMessage) -- 12
  | symbolIndexMappingRequestMessage (message : SymbolIndexMappingRequestMessage) -- 13
  | refreshRequestMessage (message : RefreshRequestMessage) -- 15
  | messageUnavailableMessage (message : MessageUnavailableMessage) -- 31
  | symbolClearMessage (message : SymbolClearMessage) -- 32
  | securityStatusMessage (message : SecurityStatusMessage) -- 34
  | refreshHeaderMessage (message : RefreshHeaderMessage) -- 35
  | outrightSeriesIndexMappingMessage (message : OutrightSeriesIndexMappingMessage) -- 50
  | optionsStatusMessage (message : OptionsStatusMessage) -- 51
  | complexSeriesIndexMappingMessage (message : ComplexSeriesIndexMappingMessage) -- 60
  | optionsQuoteMessage (message : OptionsQuoteMessage) -- 340
  | optionsTradeMessage (message : OptionsTradeMessage) -- 320
  | seriesRfqMessage (message : SeriesRfqMessage) -- 307
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceNumberResetMessage _ => 1
  | .timeReferenceMessage _ => 2
  | .symbolIndexMappingMessage _ => 3
  | .retransmissionRequestMessage _ => 10
  | .requestResponseMessage _ => 11
  | .heartbeatResponseMessage _ => 12
  | .symbolIndexMappingRequestMessage _ => 13
  | .refreshRequestMessage _ => 15
  | .messageUnavailableMessage _ => 31
  | .symbolClearMessage _ => 32
  | .securityStatusMessage _ => 34
  | .refreshHeaderMessage _ => 35
  | .outrightSeriesIndexMappingMessage _ => 50
  | .optionsStatusMessage _ => 51
  | .complexSeriesIndexMappingMessage _ => 60
  | .optionsQuoteMessage _ => 340
  | .optionsTradeMessage _ => 320
  | .seriesRfqMessage _ => 307

def encode : Payload → List UInt8
  | .sequenceNumberResetMessage message => SequenceNumberResetMessage.encode message
  | .timeReferenceMessage message => TimeReferenceMessage.encode message
  | .symbolIndexMappingMessage message => SymbolIndexMappingMessage.encode message
  | .retransmissionRequestMessage message => RetransmissionRequestMessage.encode message
  | .requestResponseMessage message => RequestResponseMessage.encode message
  | .heartbeatResponseMessage message => HeartbeatResponseMessage.encode message
  | .symbolIndexMappingRequestMessage message => SymbolIndexMappingRequestMessage.encode message
  | .refreshRequestMessage message => RefreshRequestMessage.encode message
  | .messageUnavailableMessage message => MessageUnavailableMessage.encode message
  | .symbolClearMessage message => SymbolClearMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .refreshHeaderMessage message => RefreshHeaderMessage.encode message
  | .outrightSeriesIndexMappingMessage message => OutrightSeriesIndexMappingMessage.encode message
  | .optionsStatusMessage message => OptionsStatusMessage.encode message
  | .complexSeriesIndexMappingMessage message => ComplexSeriesIndexMappingMessage.encode message
  | .optionsQuoteMessage message => OptionsQuoteMessage.encode message
  | .optionsTradeMessage message => OptionsTradeMessage.encode message
  | .seriesRfqMessage message => SeriesRfqMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 524289 := by
  cases message with
  | sequenceNumberResetMessage inner =>
    simp only [encode, SequenceNumberResetMessage.encode_length]
    omega
  | timeReferenceMessage inner =>
    simp only [encode, TimeReferenceMessage.encode_length]
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
  | symbolClearMessage inner =>
    simp only [encode, SymbolClearMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | refreshHeaderMessage inner =>
    have bound_inner := RefreshHeaderMessage.encode_length_le inner
    simp only [encode]
    omega
  | outrightSeriesIndexMappingMessage inner =>
    simp only [encode, OutrightSeriesIndexMappingMessage.encode_length]
    omega
  | optionsStatusMessage inner =>
    simp only [encode, OptionsStatusMessage.encode_length]
    omega
  | complexSeriesIndexMappingMessage inner =>
    have bound_inner := ComplexSeriesIndexMappingMessage.encode_length_le inner
    simp only [encode]
    omega
  | optionsQuoteMessage inner =>
    simp only [encode, OptionsQuoteMessage.encode_length]
    omega
  | optionsTradeMessage inner =>
    simp only [encode, OptionsTradeMessage.encode_length]
    omega
  | seriesRfqMessage inner =>
    simp only [encode, SeriesRfqMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (SequenceNumberResetMessage.decode bytes).map fun (message, rest) => (.sequenceNumberResetMessage message, rest)
  else if tag = 2 then (TimeReferenceMessage.decode bytes).map fun (message, rest) => (.timeReferenceMessage message, rest)
  else if tag = 3 then (SymbolIndexMappingMessage.decode bytes).map fun (message, rest) => (.symbolIndexMappingMessage message, rest)
  else if tag = 10 then (RetransmissionRequestMessage.decode bytes).map fun (message, rest) => (.retransmissionRequestMessage message, rest)
  else if tag = 11 then (RequestResponseMessage.decode bytes).map fun (message, rest) => (.requestResponseMessage message, rest)
  else if tag = 12 then (HeartbeatResponseMessage.decode bytes).map fun (message, rest) => (.heartbeatResponseMessage message, rest)
  else if tag = 13 then (SymbolIndexMappingRequestMessage.decode bytes).map fun (message, rest) => (.symbolIndexMappingRequestMessage message, rest)
  else if tag = 15 then (RefreshRequestMessage.decode bytes).map fun (message, rest) => (.refreshRequestMessage message, rest)
  else if tag = 31 then (MessageUnavailableMessage.decode bytes).map fun (message, rest) => (.messageUnavailableMessage message, rest)
  else if tag = 32 then (SymbolClearMessage.decode bytes).map fun (message, rest) => (.symbolClearMessage message, rest)
  else if tag = 34 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 35 then (RefreshHeaderMessage.decode bytes).map fun (message, rest) => (.refreshHeaderMessage message, rest)
  else if tag = 50 then (OutrightSeriesIndexMappingMessage.decode bytes).map fun (message, rest) => (.outrightSeriesIndexMappingMessage message, rest)
  else if tag = 51 then (OptionsStatusMessage.decode bytes).map fun (message, rest) => (.optionsStatusMessage message, rest)
  else if tag = 60 then (ComplexSeriesIndexMappingMessage.decode bytes).map fun (message, rest) => (.complexSeriesIndexMappingMessage message, rest)
  else if tag = 340 then (OptionsQuoteMessage.decode bytes).map fun (message, rest) => (.optionsQuoteMessage message, rest)
  else if tag = 320 then (OptionsTradeMessage.decode bytes).map fun (message, rest) => (.optionsTradeMessage message, rest)
  else if tag = 307 then (SeriesRfqMessage.decode bytes).map fun (message, rest) => (.seriesRfqMessage message, rest)
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

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
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
  pktSize : BitVec 16
  deliveryFlag : BitVec 8
  seqNum : BitVec 32
  sendTime : SendTime
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.pktSize
    ++ (encodeUIntLE 1 message.deliveryFlag
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUIntLE 4 message.seqNum
    ++ (SendTime.encode message.sendTime
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (pktSize, bytes) ← decodeUIntLE 2 bytes
  let (deliveryFlag, bytes) ← decodeUIntLE 1 bytes
  let (numberMsgs, bytes) ← decodeUIntLE 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← SendTime.decode bytes
  let (message_, bytes) ← decodeMany Message.decode numberMsgs.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ pktSize, deliveryFlag, seqNum, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
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

end Omi.NyseArcaoptionsComplexfeedPillarV10D
