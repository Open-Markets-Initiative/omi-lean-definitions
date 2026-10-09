import Wire

/-!
# New York Stock Exchange Best Bid And Offer v2.5.d

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseNationalequitiesBboPillarV25D

/-- Exchange Code: one byte code -/
def ExchangeCode.codes : List UInt8 :=
  [0x41, 0x4C, 0x4E, 0x50, 0x51, 0x56, 0x5A]

inductive ExchangeCode where
  | nyseAmerican -- Nyse American
  | ltse -- Ltse
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | iex -- Iex
  | cboe -- Cboe
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
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExchangeCode :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x4C then .ltse
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x56 then .iex
  else .cboe

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
  | lateSessionNonNyseOnly -- Late Session Non Nyse Only
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
  | .lateSessionNonNyseOnly => 0x4C
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
  else if byte = 0x4C then .lateSessionNonNyseOnly
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
  | lateSessionNonNyseOnly => decide
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
  [0x7E, 0x44, 0x49, 0x50, 0x4D, 0x58, 0x41, 0x43, 0x45, 0x46, 0x4E, 0x4F, 0x56, 0x36, 0x31, 0x32, 0x33]

inductive HaltCondition where
  | securityNotDelayedhalted -- Security Not Delayedhalted
  | newsReleasedNewsDissemination -- News Released News Dissemination
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
  | suspend -- Suspend
  | marketWideCircuitBreakerHaltLevel1 -- Market Wide Circuit Breaker Halt Level 1
  | marketWideCircuitBreakerHaltLevel2 -- Market Wide Circuit Breaker Halt Level 2
  | marketWideCircuitBreakerHaltLevel3 -- Market Wide Circuit Breaker Halt Level 3
  | unlisted (byte : { byte : UInt8 // byte ∉ HaltCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HaltCondition

def toByte : HaltCondition → UInt8
  | .securityNotDelayedhalted => 0x7E
  | .newsReleasedNewsDissemination => 0x44
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
  | .suspend => 0x36
  | .marketWideCircuitBreakerHaltLevel1 => 0x31
  | .marketWideCircuitBreakerHaltLevel2 => 0x32
  | .marketWideCircuitBreakerHaltLevel3 => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HaltCondition :=
  if byte = 0x7E then .securityNotDelayedhalted
  else if byte = 0x44 then .newsReleasedNewsDissemination
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
  else if byte = 0x36 then .suspend
  else if byte = 0x31 then .marketWideCircuitBreakerHaltLevel1
  else if byte = 0x32 then .marketWideCircuitBreakerHaltLevel2
  else .marketWideCircuitBreakerHaltLevel3

def ofByte (byte : UInt8) : HaltCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HaltCondition) : ofByte value.toByte = value := by
  cases value with
  | securityNotDelayedhalted => decide
  | newsReleasedNewsDissemination => decide
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
  | suspend => decide
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
  [0x41, 0x42, 0x43, 0x44, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x20]

inductive SsrTriggeringExchangeId where
  | nyseAmerican -- Nyse American
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nyseNational -- Nyse National
  | finra -- Finra
  | miamiPeral -- Miami Peral
  | nasdaqIse -- Nasdaq Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseTexas -- Nyse Texas
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | nasdaqOmx -- Nasdaq Omx
  | memx -- Memx
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqOmxPsx -- Nasdaq Omx Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | noValue -- No Value
  | unlisted (byte : { byte : UInt8 // byte ∉ SsrTriggeringExchangeId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SsrTriggeringExchangeId

def toByte : SsrTriggeringExchangeId → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqOmxBx => 0x42
  | .nyseNational => 0x43
  | .finra => 0x44
  | .miamiPeral => 0x48
  | .nasdaqIse => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseTexas => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .nasdaqOmx => 0x54
  | .memx => 0x55
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqOmxPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .noValue => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SsrTriggeringExchangeId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqOmxBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finra
  else if byte = 0x48 then .miamiPeral
  else if byte = 0x49 then .nasdaqIse
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x54 then .nasdaqOmx
  else if byte = 0x55 then .memx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqOmxPsx
  else if byte = 0x59 then .cboeByx
  else if byte = 0x5A then .cboeBzx
  else .noValue

def ofByte (byte : UInt8) : SsrTriggeringExchangeId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SsrTriggeringExchangeId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqOmxBx => decide
  | nyseNational => decide
  | finra => decide
  | miamiPeral => decide
  | nasdaqIse => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseTexas => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | nasdaqOmx => decide
  | memx => decide
  | iex => decide
  | cbsx => decide
  | nasdaqOmxPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
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
  | lateSessionNonNyseOnly -- Late Session Non Nyse Only
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketState

def toByte : MarketState → UInt8
  | .preopening => 0x50
  | .earlySession => 0x45
  | .coreSession => 0x4F
  | .lateSessionNonNyseOnly => 0x4C
  | .closed => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketState :=
  if byte = 0x50 then .preopening
  else if byte = 0x45 then .earlySession
  else if byte = 0x4F then .coreSession
  else if byte = 0x4C then .lateSessionNonNyseOnly
  else .closed

def ofByte (byte : UInt8) : MarketState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketState) : ofByte value.toByte = value := by
  cases value with
  | preopening => decide
  | earlySession => decide
  | coreSession => decide
  | lateSessionNonNyseOnly => decide
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

/-- Status: one byte code -/
def Status.codes : List UInt8 :=
  [0x30, 0x31, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]

inductive Status where
  | messageWasAccepted -- Message Was Accepted
  | rejectedDueToAnInvalidSourceId -- Rejected Due To An Invalid Source Id
  | rejectedDueToMaximumSequenceRangeSeeThresholdLimits -- Rejected Due To Maximum Sequence Range See Threshold Limits
  | rejectedDueToMaximumRequestInADay -- Rejected Due To Maximum Request In A Day
  | rejectedDueToMaximumNumberOfRefreshRequestsInADay -- Rejected Due To Maximum Number Of Refresh Requests In A Day
  | rejectedRequestMessageSeqNumTtlTimeToLiveIsTooOldUseRefreshToRecoverCurrentStateIfNecessary -- Rejected Request Message Seq Num Ttl Time To Live Is Too Old Use Refresh To Recover Current State If Necessary
  | rejectedDueToAnInvalidChannelId -- Rejected Due To An Invalid Channel Id
  | rejectedDueToAnInvalidProductId -- Rejected Due To An Invalid Product Id
  | rejectedDueTo1InvalidMsgTypeOr2MismatchBetweenMsgTypeAndMsgSize -- Rejected Due To 1 Invalid Msg Type Or 2 Mismatch Between Msg Type And Msg Size
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .messageWasAccepted => 0x30
  | .rejectedDueToAnInvalidSourceId => 0x31
  | .rejectedDueToMaximumSequenceRangeSeeThresholdLimits => 0x33
  | .rejectedDueToMaximumRequestInADay => 0x34
  | .rejectedDueToMaximumNumberOfRefreshRequestsInADay => 0x35
  | .rejectedRequestMessageSeqNumTtlTimeToLiveIsTooOldUseRefreshToRecoverCurrentStateIfNecessary => 0x36
  | .rejectedDueToAnInvalidChannelId => 0x37
  | .rejectedDueToAnInvalidProductId => 0x38
  | .rejectedDueTo1InvalidMsgTypeOr2MismatchBetweenMsgTypeAndMsgSize => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x30 then .messageWasAccepted
  else if byte = 0x31 then .rejectedDueToAnInvalidSourceId
  else if byte = 0x33 then .rejectedDueToMaximumSequenceRangeSeeThresholdLimits
  else if byte = 0x34 then .rejectedDueToMaximumRequestInADay
  else if byte = 0x35 then .rejectedDueToMaximumNumberOfRefreshRequestsInADay
  else if byte = 0x36 then .rejectedRequestMessageSeqNumTtlTimeToLiveIsTooOldUseRefreshToRecoverCurrentStateIfNecessary
  else if byte = 0x37 then .rejectedDueToAnInvalidChannelId
  else if byte = 0x38 then .rejectedDueToAnInvalidProductId
  else .rejectedDueTo1InvalidMsgTypeOr2MismatchBetweenMsgTypeAndMsgSize

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | messageWasAccepted => decide
  | rejectedDueToAnInvalidSourceId => decide
  | rejectedDueToMaximumSequenceRangeSeeThresholdLimits => decide
  | rejectedDueToMaximumRequestInADay => decide
  | rejectedDueToMaximumNumberOfRefreshRequestsInADay => decide
  | rejectedRequestMessageSeqNumTtlTimeToLiveIsTooOldUseRefreshToRecoverCurrentStateIfNecessary => decide
  | rejectedDueToAnInvalidChannelId => decide
  | rejectedDueToAnInvalidProductId => decide
  | rejectedDueTo1InvalidMsgTypeOr2MismatchBetweenMsgTypeAndMsgSize => decide
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

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x52, 0x4F]

inductive QuoteCondition where
  | regularQuote -- Regular Quote
  | openingQuote -- Opening Quote
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .regularQuote => 0x52
  | .openingQuote => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x52 then .regularQuote
  else .openingQuote

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | regularQuote => decide
  | openingQuote => decide
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
  | noRetailInterestDefault -- No Retail Interest Default
  | retailInterestOnBidSide -- Retail Interest On Bid Side
  | retailInterestOnOfferSide -- Retail Interest On Offer Side
  | retailInterestOnTheBidAndOfferSide -- Retail Interest On The Bid And Offer Side
  | unlisted (byte : { byte : UInt8 // byte ∉ RpiIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RpiIndicator

def toByte : RpiIndicator → UInt8
  | .noRetailInterestDefault => 0x20
  | .retailInterestOnBidSide => 0x41
  | .retailInterestOnOfferSide => 0x42
  | .retailInterestOnTheBidAndOfferSide => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RpiIndicator :=
  if byte = 0x20 then .noRetailInterestDefault
  else if byte = 0x41 then .retailInterestOnBidSide
  else if byte = 0x42 then .retailInterestOnOfferSide
  else .retailInterestOnTheBidAndOfferSide

def ofByte (byte : UInt8) : RpiIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RpiIndicator) : ofByte value.toByte = value := by
  cases value with
  | noRetailInterestDefault => decide
  | retailInterestOnBidSide => decide
  | retailInterestOnOfferSide => decide
  | retailInterestOnTheBidAndOfferSide => decide
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

/-- Source Time Reference Message: 12 bytes -/
structure SourceTimeReferenceMessage where
  id : BitVec 32
  symbolSeqNum : BitVec 32
  sourceTime : BitVec 32
  deriving DecidableEq, Repr

namespace SourceTimeReferenceMessage

def encode (message : SourceTimeReferenceMessage) : List UInt8 :=
  encodeUIntLE 4 message.id
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.sourceTime))

def decode (bytes : List UInt8) : Option (SourceTimeReferenceMessage × List UInt8) := do
  let (id, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  pure ({ id, symbolSeqNum, sourceTime }, bytes)

@[simp] theorem encode_length (message : SourceTimeReferenceMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SourceTimeReferenceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SourceTimeReferenceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SourceTimeReferenceMessage

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
  sessionState : Alpha 1
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
    ++ (Alpha.encode message.sessionState))))))))))))))

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
  let (sessionState, bytes) ← Alpha.decode 1 bytes
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityStatusMessage

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

/-- Quote Message: 30 bytes -/
structure QuoteMessage where
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  askPrice : BitVec 32
  askVolume : BitVec 32
  bidPrice : BitVec 32
  bidVolume : BitVec 32
  quoteCondition : QuoteCondition
  rpiIndicator : RpiIndicator
  deriving DecidableEq, Repr

namespace QuoteMessage

def encode (message : QuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.askPrice
    ++ (encodeUIntLE 4 message.askVolume
    ++ (encodeUIntLE 4 message.bidPrice
    ++ (encodeUIntLE 4 message.bidVolume
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (RpiIndicator.encode message.rpiIndicator))))))))

def decode (bytes : List UInt8) : Option (QuoteMessage × List UInt8) := do
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (askPrice, bytes) ← decodeUIntLE 4 bytes
  let (askVolume, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 4 bytes
  let (bidVolume, bytes) ← decodeUIntLE 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (rpiIndicator, bytes) ← RpiIndicator.decode bytes
  pure ({ sourceTimeNs, symbolIndex, symbolSeqNum, askPrice, askVolume, bidPrice, bidVolume, quoteCondition, rpiIndicator }, bytes)

@[simp] theorem encode_length (message : QuoteMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, QuoteCondition.encode_length, RpiIndicator.encode_length]

theorem encode_length_pos (message : QuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteMessage) (rest : List UInt8) :
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
  rw [RpiIndicator.decode_encode, some_bind]
  rfl

end QuoteMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | sequenceNumberResetMessage (message : SequenceNumberResetMessage) -- 1
  | sourceTimeReferenceMessage (message : SourceTimeReferenceMessage) -- 2
  | symbolIndexMappingMessage (message : SymbolIndexMappingMessage) -- 3
  | symbolClearMessage (message : SymbolClearMessage) -- 32
  | securityStatusMessage (message : SecurityStatusMessage) -- 34
  | retransmissionRequestMessage (message : RetransmissionRequestMessage) -- 10
  | symbolIndexMappingRequestMessage (message : SymbolIndexMappingRequestMessage) -- 13
  | refreshRequestMessage (message : RefreshRequestMessage) -- 15
  | messageUnavailableMessage (message : MessageUnavailableMessage) -- 31
  | refreshHeaderMessage (message : RefreshHeaderMessage) -- 35
  | requestResponseMessage (message : RequestResponseMessage) -- 11
  | heartbeatResponseMessage (message : HeartbeatResponseMessage) -- 12
  | quoteMessage (message : QuoteMessage) -- 140
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceNumberResetMessage _ => 1
  | .sourceTimeReferenceMessage _ => 2
  | .symbolIndexMappingMessage _ => 3
  | .symbolClearMessage _ => 32
  | .securityStatusMessage _ => 34
  | .retransmissionRequestMessage _ => 10
  | .symbolIndexMappingRequestMessage _ => 13
  | .refreshRequestMessage _ => 15
  | .messageUnavailableMessage _ => 31
  | .refreshHeaderMessage _ => 35
  | .requestResponseMessage _ => 11
  | .heartbeatResponseMessage _ => 12
  | .quoteMessage _ => 140

def encode : Payload → List UInt8
  | .sequenceNumberResetMessage message => SequenceNumberResetMessage.encode message
  | .sourceTimeReferenceMessage message => SourceTimeReferenceMessage.encode message
  | .symbolIndexMappingMessage message => SymbolIndexMappingMessage.encode message
  | .symbolClearMessage message => SymbolClearMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .retransmissionRequestMessage message => RetransmissionRequestMessage.encode message
  | .symbolIndexMappingRequestMessage message => SymbolIndexMappingRequestMessage.encode message
  | .refreshRequestMessage message => RefreshRequestMessage.encode message
  | .messageUnavailableMessage message => MessageUnavailableMessage.encode message
  | .refreshHeaderMessage message => RefreshHeaderMessage.encode message
  | .requestResponseMessage message => RequestResponseMessage.encode message
  | .heartbeatResponseMessage message => HeartbeatResponseMessage.encode message
  | .quoteMessage message => QuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 42 := by
  cases message with
  | sequenceNumberResetMessage inner =>
    simp only [encode, SequenceNumberResetMessage.encode_length]
    omega
  | sourceTimeReferenceMessage inner =>
    simp only [encode, SourceTimeReferenceMessage.encode_length]
    omega
  | symbolIndexMappingMessage inner =>
    simp only [encode, SymbolIndexMappingMessage.encode_length]
    omega
  | symbolClearMessage inner =>
    simp only [encode, SymbolClearMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [encode, RetransmissionRequestMessage.encode_length]
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
  | refreshHeaderMessage inner =>
    have bound_inner := RefreshHeaderMessage.encode_length_le inner
    simp only [encode]
    omega
  | requestResponseMessage inner =>
    simp only [encode, RequestResponseMessage.encode_length]
    omega
  | heartbeatResponseMessage inner =>
    simp only [encode, HeartbeatResponseMessage.encode_length]
    omega
  | quoteMessage inner =>
    simp only [encode, QuoteMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (SequenceNumberResetMessage.decode bytes).map fun (message, rest) => (.sequenceNumberResetMessage message, rest)
  else if tag = 2 then (SourceTimeReferenceMessage.decode bytes).map fun (message, rest) => (.sourceTimeReferenceMessage message, rest)
  else if tag = 3 then (SymbolIndexMappingMessage.decode bytes).map fun (message, rest) => (.symbolIndexMappingMessage message, rest)
  else if tag = 32 then (SymbolClearMessage.decode bytes).map fun (message, rest) => (.symbolClearMessage message, rest)
  else if tag = 34 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 10 then (RetransmissionRequestMessage.decode bytes).map fun (message, rest) => (.retransmissionRequestMessage message, rest)
  else if tag = 13 then (SymbolIndexMappingRequestMessage.decode bytes).map fun (message, rest) => (.symbolIndexMappingRequestMessage message, rest)
  else if tag = 15 then (RefreshRequestMessage.decode bytes).map fun (message, rest) => (.refreshRequestMessage message, rest)
  else if tag = 31 then (MessageUnavailableMessage.decode bytes).map fun (message, rest) => (.messageUnavailableMessage message, rest)
  else if tag = 35 then (RefreshHeaderMessage.decode bytes).map fun (message, rest) => (.refreshHeaderMessage message, rest)
  else if tag = 11 then (RequestResponseMessage.decode bytes).map fun (message, rest) => (.requestResponseMessage message, rest)
  else if tag = 12 then (HeartbeatResponseMessage.decode bytes).map fun (message, rest) => (.heartbeatResponseMessage message, rest)
  else if tag = 140 then (QuoteMessage.decode bytes).map fun (message, rest) => (.quoteMessage message, rest)
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
  | sourceTimeReferenceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SourceTimeReferenceMessage.encode_length]
    omega
  | symbolIndexMappingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SymbolIndexMappingMessage.encode_length]
    omega
  | symbolClearMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SymbolClearMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SecurityStatusMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RetransmissionRequestMessage.encode_length]
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
  | refreshHeaderMessage inner =>
    have bound_inner := RefreshHeaderMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | requestResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RequestResponseMessage.encode_length]
    omega
  | heartbeatResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, HeartbeatResponseMessage.encode_length]
    omega
  | quoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, QuoteMessage.encode_length]
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

end Omi.NyseNationalequitiesBboPillarV25D
