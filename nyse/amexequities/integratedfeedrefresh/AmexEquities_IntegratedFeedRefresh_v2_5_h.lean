import Wire

/-!
# New York Stock Exchange Integrated Feed Refresh v2.5.h

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseAmexequitiesIntegratedfeedrefreshPillarV25H

/-- Exchange Code: one byte code -/
def ExchangeCode.codes : List UInt8 :=
  [0x46, 0x41, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x56, 0x5A]

inductive ExchangeCode where
  | txse -- Txse
  | nyseAmerican -- Nyse American
  | ltse -- Ltse
  | nyseTexas -- Nyse Texas
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | iex -- Iex
  | cboe -- Cboe
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeCode

def toByte : ExchangeCode → UInt8
  | .txse => 0x46
  | .nyseAmerican => 0x41
  | .ltse => 0x4C
  | .nyseTexas => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .iex => 0x56
  | .cboe => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExchangeCode :=
  if byte = 0x46 then .txse
  else if byte = 0x41 then .nyseAmerican
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x56 then .iex
  else .cboe

def ofByte (byte : UInt8) : ExchangeCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeCode) : ofByte value.toByte = value := by
  cases value with
  | txse => decide
  | nyseAmerican => decide
  | ltse => decide
  | nyseTexas => decide
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
  [0x34, 0x35, 0x36, 0x41, 0x43, 0x44, 0x50, 0x42, 0x4E, 0x45, 0x4F, 0x4C, 0x58, 0x49, 0x47]

inductive SecurityStatus where
  | tradingHalt -- Trading Halt
  | resume -- Resume
  | suspendOperationalHalt -- Suspend Operational Halt
  | shortSaleRestrictionActivatedDay1 -- Short Sale Restriction Activated Day 1
  | shortSaleRestrictionContinuedDay2 -- Short Sale Restriction Continued Day 2
  | shortSaleRestrictionDeactivated -- Short Sale Restriction Deactivated
  | preopening -- Preopening
  | beginAcceptingOrders -- Begin Accepting Orders
  | overnightSession -- Overnight Session
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
  | .suspendOperationalHalt => 0x36
  | .shortSaleRestrictionActivatedDay1 => 0x41
  | .shortSaleRestrictionContinuedDay2 => 0x43
  | .shortSaleRestrictionDeactivated => 0x44
  | .preopening => 0x50
  | .beginAcceptingOrders => 0x42
  | .overnightSession => 0x4E
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
  else if byte = 0x36 then .suspendOperationalHalt
  else if byte = 0x41 then .shortSaleRestrictionActivatedDay1
  else if byte = 0x43 then .shortSaleRestrictionContinuedDay2
  else if byte = 0x44 then .shortSaleRestrictionDeactivated
  else if byte = 0x50 then .preopening
  else if byte = 0x42 then .beginAcceptingOrders
  else if byte = 0x4E then .overnightSession
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
  | suspendOperationalHalt => decide
  | shortSaleRestrictionActivatedDay1 => decide
  | shortSaleRestrictionContinuedDay2 => decide
  | shortSaleRestrictionDeactivated => decide
  | preopening => decide
  | beginAcceptingOrders => decide
  | overnightSession => decide
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
  | sipOutageMaterialSipLatencyOrExtraordinaryMarketActivity -- Sip Outage Material Sip Latency Or Extraordinary Market Activity
  | regulatoryConcern -- Regulatory Concern
  | mergerEffective -- Merger Effective
  | etfIivEtfComponentPricesNotAvailable -- Etf Iiv Etf Component Prices Not Available
  | corporateAction -- Corporate Action
  | newSecurityOffering -- New Security Offering
  | primaryListingExchangeDiscretionaryHalt -- Primary Listing Exchange Discretionary Halt
  | suspendOperationalHalt -- Suspend Operational Halt
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
  | .sipOutageMaterialSipLatencyOrExtraordinaryMarketActivity => 0x41
  | .regulatoryConcern => 0x43
  | .mergerEffective => 0x45
  | .etfIivEtfComponentPricesNotAvailable => 0x46
  | .corporateAction => 0x4E
  | .newSecurityOffering => 0x4F
  | .primaryListingExchangeDiscretionaryHalt => 0x56
  | .suspendOperationalHalt => 0x36
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
  else if byte = 0x41 then .sipOutageMaterialSipLatencyOrExtraordinaryMarketActivity
  else if byte = 0x43 then .regulatoryConcern
  else if byte = 0x45 then .mergerEffective
  else if byte = 0x46 then .etfIivEtfComponentPricesNotAvailable
  else if byte = 0x4E then .corporateAction
  else if byte = 0x4F then .newSecurityOffering
  else if byte = 0x56 then .primaryListingExchangeDiscretionaryHalt
  else if byte = 0x36 then .suspendOperationalHalt
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
  | sipOutageMaterialSipLatencyOrExtraordinaryMarketActivity => decide
  | regulatoryConcern => decide
  | mergerEffective => decide
  | etfIivEtfComponentPricesNotAvailable => decide
  | corporateAction => decide
  | newSecurityOffering => decide
  | primaryListingExchangeDiscretionaryHalt => decide
  | suspendOperationalHalt => decide
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
  [0x41, 0x42, 0x43, 0x44, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x20]

inductive SsrTriggeringExchangeId where
  | nyseAmerican -- Nyse American
  | nasdaqOmsTx -- Nasdaq Oms Tx
  | nyseNational -- Nyse National
  | finra -- Finra
  | n24X -- N 24 X
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
  | .nasdaqOmsTx => 0x42
  | .nyseNational => 0x43
  | .finra => 0x44
  | .n24X => 0x47
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
  else if byte = 0x42 then .nasdaqOmsTx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finra
  else if byte = 0x47 then .n24X
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
  | nasdaqOmsTx => decide
  | nyseNational => decide
  | finra => decide
  | n24X => decide
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
  [0x50, 0x4E, 0x45, 0x4F, 0x4C, 0x58]

inductive MarketState where
  | preopening -- Preopening
  | overnightSession -- Overnight Session
  | earlySession -- Early Session
  | coreSession -- Core Session
  | lateSessionNonNyseOnly -- Late Session Non Nyse Only
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketState

def toByte : MarketState → UInt8
  | .preopening => 0x50
  | .overnightSession => 0x4E
  | .earlySession => 0x45
  | .coreSession => 0x4F
  | .lateSessionNonNyseOnly => 0x4C
  | .closed => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketState :=
  if byte = 0x50 then .preopening
  else if byte = 0x4E then .overnightSession
  else if byte = 0x45 then .earlySession
  else if byte = 0x4F then .coreSession
  else if byte = 0x4C then .lateSessionNonNyseOnly
  else .closed

def ofByte (byte : UInt8) : MarketState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketState) : ofByte value.toByte = value := by
  cases value with
  | preopening => decide
  | overnightSession => decide
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

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x4F, 0x4D, 0x48, 0x43, 0x50, 0x52]

inductive AuctionType where
  | earlyOpeningAuction -- Early Opening Auction
  | coreOpeningAuction -- Core Opening Auction
  | reopeningAuctionHaltResume -- Reopening Auction Halt Resume
  | closingAuction -- Closing Auction
  | extremeClosingImbalance -- Extreme Closing Imbalance
  | significantClosingImbalance -- Significant Closing Imbalance
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .earlyOpeningAuction => 0x4F
  | .coreOpeningAuction => 0x4D
  | .reopeningAuctionHaltResume => 0x48
  | .closingAuction => 0x43
  | .extremeClosingImbalance => 0x50
  | .significantClosingImbalance => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x4F then .earlyOpeningAuction
  else if byte = 0x4D then .coreOpeningAuction
  else if byte = 0x48 then .reopeningAuctionHaltResume
  else if byte = 0x43 then .closingAuction
  else if byte = 0x50 then .extremeClosingImbalance
  else .significantClosingImbalance

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | earlyOpeningAuction => decide
  | coreOpeningAuction => decide
  | reopeningAuctionHaltResume => decide
  | closingAuction => decide
  | extremeClosingImbalance => decide
  | significantClosingImbalance => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AuctionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionType

/-- Imbalance Side: one byte code -/
def ImbalanceSide.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive ImbalanceSide where
  | buySide -- Buy Side
  | sellSide -- Sell Side
  | noImbalance -- No Imbalance
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceSide

def toByte : ImbalanceSide → UInt8
  | .buySide => 0x42
  | .sellSide => 0x53
  | .noImbalance => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceSide :=
  if byte = 0x42 then .buySide
  else if byte = 0x53 then .sellSide
  else .noImbalance

def ofByte (byte : UInt8) : ImbalanceSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceSide) : ofByte value.toByte = value := by
  cases value with
  | buySide => decide
  | sellSide => decide
  | noImbalance => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ImbalanceSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ImbalanceSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ImbalanceSide

/-- Unpaired Side: one byte code -/
def UnpairedSide.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive UnpairedSide where
  | buySide -- Buy Side
  | sellSide -- Sell Side
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ UnpairedSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UnpairedSide

def toByte : UnpairedSide → UInt8
  | .buySide => 0x42
  | .sellSide => 0x53
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UnpairedSide :=
  if byte = 0x42 then .buySide
  else if byte = 0x53 then .sellSide
  else .notApplicable

def ofByte (byte : UInt8) : UnpairedSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UnpairedSide) : ofByte value.toByte = value := by
  cases value with
  | buySide => decide
  | sellSide => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UnpairedSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UnpairedSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UnpairedSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : UnpairedSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UnpairedSide

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
  lateCloseEligible : BitVec 8
  ethEligible : BitVec 8
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
    ++ (encodeUIntLE 1 message.lateCloseEligible
    ++ (encodeUIntLE 1 message.ethEligible))))))))))))))))

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
  let (lateCloseEligible, bytes) ← decodeUIntLE 1 bytes
  let (ethEligible, bytes) ← decodeUIntLE 1 bytes
  pure ({ symbolIndex, symbol, reserved1, marketId, systemId, exchangeCode, priceScaleCode, securityType, lotSize, prevClosePrice, prevCloseVolume, priceResolution, roundLot, mpv, unitOfTrade, lateCloseEligible, ethEligible }, bytes)

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SymbolIndexMappingMessage

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

/-- Imbalance Message: 69 bytes -/
structure ImbalanceMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  referencePrice : BitVec 32
  pairedQty : BitVec 32
  totalImbalanceQty : BitVec 32
  marketImbalanceQty : BitVec 32
  auctionTime : BitVec 16
  auctionType : AuctionType
  imbalanceSide : ImbalanceSide
  continuousBookClearingPrice : BitVec 32
  auctionInterestClearingPrice : BitVec 32
  ssrFilingPrice : BitVec 32
  indicativeMatchPrice : BitVec 32
  upperCollar : BitVec 32
  lowerCollar : BitVec 32
  auctionStatus : BitVec 8
  freezeStatus : BitVec 8
  numExtensions : BitVec 8
  unpairedQty : BitVec 32
  unpairedSide : UnpairedSide
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace ImbalanceMessage

def encode (message : ImbalanceMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.referencePrice
    ++ (encodeUIntLE 4 message.pairedQty
    ++ (encodeUIntLE 4 message.totalImbalanceQty
    ++ (encodeUIntLE 4 message.marketImbalanceQty
    ++ (encodeUIntLE 2 message.auctionTime
    ++ (AuctionType.encode message.auctionType
    ++ (ImbalanceSide.encode message.imbalanceSide
    ++ (encodeUIntLE 4 message.continuousBookClearingPrice
    ++ (encodeUIntLE 4 message.auctionInterestClearingPrice
    ++ (encodeUIntLE 4 message.ssrFilingPrice
    ++ (encodeUIntLE 4 message.indicativeMatchPrice
    ++ (encodeUIntLE 4 message.upperCollar
    ++ (encodeUIntLE 4 message.lowerCollar
    ++ (encodeUIntLE 1 message.auctionStatus
    ++ (encodeUIntLE 1 message.freezeStatus
    ++ (encodeUIntLE 1 message.numExtensions
    ++ (encodeUIntLE 4 message.unpairedQty
    ++ (UnpairedSide.encode message.unpairedSide
    ++ (Alpha.encode message.reserved1))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ImbalanceMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (referencePrice, bytes) ← decodeUIntLE 4 bytes
  let (pairedQty, bytes) ← decodeUIntLE 4 bytes
  let (totalImbalanceQty, bytes) ← decodeUIntLE 4 bytes
  let (marketImbalanceQty, bytes) ← decodeUIntLE 4 bytes
  let (auctionTime, bytes) ← decodeUIntLE 2 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (imbalanceSide, bytes) ← ImbalanceSide.decode bytes
  let (continuousBookClearingPrice, bytes) ← decodeUIntLE 4 bytes
  let (auctionInterestClearingPrice, bytes) ← decodeUIntLE 4 bytes
  let (ssrFilingPrice, bytes) ← decodeUIntLE 4 bytes
  let (indicativeMatchPrice, bytes) ← decodeUIntLE 4 bytes
  let (upperCollar, bytes) ← decodeUIntLE 4 bytes
  let (lowerCollar, bytes) ← decodeUIntLE 4 bytes
  let (auctionStatus, bytes) ← decodeUIntLE 1 bytes
  let (freezeStatus, bytes) ← decodeUIntLE 1 bytes
  let (numExtensions, bytes) ← decodeUIntLE 1 bytes
  let (unpairedQty, bytes) ← decodeUIntLE 4 bytes
  let (unpairedSide, bytes) ← UnpairedSide.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, referencePrice, pairedQty, totalImbalanceQty, marketImbalanceQty, auctionTime, auctionType, imbalanceSide, continuousBookClearingPrice, auctionInterestClearingPrice, ssrFilingPrice, indicativeMatchPrice, upperCollar, lowerCollar, auctionStatus, freezeStatus, numExtensions, unpairedQty, unpairedSide, reserved1 }, bytes)

@[simp] theorem encode_length (message : ImbalanceMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, AuctionType.encode_length, ImbalanceSide.encode_length, UnpairedSide.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ImbalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImbalanceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ImbalanceSide.decode_encode, some_bind]
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
  rw [List.append_assoc, UnpairedSide.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ImbalanceMessage

/-- Add Order Refresh Message: 39 bytes -/
structure AddOrderRefreshMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  symbolIndex : BitVec 32
  symbolSeqNum : BitVec 32
  orderId : BitVec 64
  price : BitVec 32
  volume : BitVec 32
  side : Side
  firmId : Alpha 5
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace AddOrderRefreshMessage

def encode (message : AddOrderRefreshMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.symbolIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (Side.encode message.side
    ++ (Alpha.encode message.firmId
    ++ (Alpha.encode message.reserved1)))))))))

def decode (bytes : List UInt8) : Option (AddOrderRefreshMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (symbolIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (firmId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ sourceTime, sourceTimeNs, symbolIndex, symbolSeqNum, orderId, price, volume, side, firmId, reserved1 }, bytes)

@[simp] theorem encode_length (message : AddOrderRefreshMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderRefreshMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderRefreshMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderRefreshMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | sequenceNumberResetMessage (message : SequenceNumberResetMessage) -- 1
  | sourceTimeReferenceMessage (message : SourceTimeReferenceMessage) -- 2
  | symbolIndexMappingMessage (message : SymbolIndexMappingMessage) -- 3
  | securityStatusMessage (message : SecurityStatusMessage) -- 34
  | refreshHeaderMessage (message : RefreshHeaderMessage) -- 35
  | imbalanceMessage (message : ImbalanceMessage) -- 105
  | addOrderRefreshMessage (message : AddOrderRefreshMessage) -- 106
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceNumberResetMessage _ => 1
  | .sourceTimeReferenceMessage _ => 2
  | .symbolIndexMappingMessage _ => 3
  | .securityStatusMessage _ => 34
  | .refreshHeaderMessage _ => 35
  | .imbalanceMessage _ => 105
  | .addOrderRefreshMessage _ => 106

def encode : Payload → List UInt8
  | .sequenceNumberResetMessage message => SequenceNumberResetMessage.encode message
  | .sourceTimeReferenceMessage message => SourceTimeReferenceMessage.encode message
  | .symbolIndexMappingMessage message => SymbolIndexMappingMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .refreshHeaderMessage message => RefreshHeaderMessage.encode message
  | .imbalanceMessage message => ImbalanceMessage.encode message
  | .addOrderRefreshMessage message => AddOrderRefreshMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 69 := by
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
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | refreshHeaderMessage inner =>
    have bound_inner := RefreshHeaderMessage.encode_length_le inner
    simp only [encode]
    omega
  | imbalanceMessage inner =>
    simp only [encode, ImbalanceMessage.encode_length]
    omega
  | addOrderRefreshMessage inner =>
    simp only [encode, AddOrderRefreshMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (SequenceNumberResetMessage.decode bytes).map fun (message, rest) => (.sequenceNumberResetMessage message, rest)
  else if tag = 2 then (SourceTimeReferenceMessage.decode bytes).map fun (message, rest) => (.sourceTimeReferenceMessage message, rest)
  else if tag = 3 then (SymbolIndexMappingMessage.decode bytes).map fun (message, rest) => (.symbolIndexMappingMessage message, rest)
  else if tag = 34 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 35 then (RefreshHeaderMessage.decode bytes).map fun (message, rest) => (.refreshHeaderMessage message, rest)
  else if tag = 105 then (ImbalanceMessage.decode bytes).map fun (message, rest) => (.imbalanceMessage message, rest)
  else if tag = 106 then (AddOrderRefreshMessage.decode bytes).map fun (message, rest) => (.addOrderRefreshMessage message, rest)
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
  | securityStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SecurityStatusMessage.encode_length]
    omega
  | refreshHeaderMessage inner =>
    have bound_inner := RefreshHeaderMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | imbalanceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ImbalanceMessage.encode_length]
    omega
  | addOrderRefreshMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AddOrderRefreshMessage.encode_length]
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

end Omi.NyseAmexequitiesIntegratedfeedrefreshPillarV25H
