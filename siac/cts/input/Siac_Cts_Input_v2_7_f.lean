import Wire

/-!
# The Securities Industry Automation Corporation  v2.7.f

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.SiacCtsInputCtaV27F

/-- Instrument Type: one byte code -/
def InstrumentType.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33]

inductive InstrumentType where
  | ctaEligibleEquity -- Cta Eligible Equity
  | localIssue -- Local Issue
  | corporateBond -- Corporate Bond
  | governmentBond -- Government Bond
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .ctaEligibleEquity => 0x30
  | .localIssue => 0x31
  | .corporateBond => 0x32
  | .governmentBond => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentType :=
  if byte = 0x30 then .ctaEligibleEquity
  else if byte = 0x31 then .localIssue
  else if byte = 0x32 then .corporateBond
  else .governmentBond

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | ctaEligibleEquity => decide
  | localIssue => decide
  | corporateBond => decide
  | governmentBond => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InstrumentType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentType

/-- Trade Reporting Facility Id: one byte code -/
def TradeReportingFacilityId.codes : List UInt8 :=
  [0x20, 0x64, 0x42, 0x4E, 0x54]

inductive TradeReportingFacilityId where
  | trfNotApplicable -- Trf Not Applicable
  | finraAdf -- Finra Adf
  | finraNasdaqTrfChicago -- Finra Nasdaq Trf Chicago
  | finraNyseTrf -- Finra Nyse Trf
  | finraNasdaqTrfCarteret -- Finra Nasdaq Trf Carteret
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeReportingFacilityId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeReportingFacilityId

def toByte : TradeReportingFacilityId → UInt8
  | .trfNotApplicable => 0x20
  | .finraAdf => 0x64
  | .finraNasdaqTrfChicago => 0x42
  | .finraNyseTrf => 0x4E
  | .finraNasdaqTrfCarteret => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeReportingFacilityId :=
  if byte = 0x20 then .trfNotApplicable
  else if byte = 0x64 then .finraAdf
  else if byte = 0x42 then .finraNasdaqTrfChicago
  else if byte = 0x4E then .finraNyseTrf
  else .finraNasdaqTrfCarteret

def ofByte (byte : UInt8) : TradeReportingFacilityId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeReportingFacilityId) : ofByte value.toByte = value := by
  cases value with
  | trfNotApplicable => decide
  | finraAdf => decide
  | finraNasdaqTrfChicago => decide
  | finraNyseTrf => decide
  | finraNasdaqTrfCarteret => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeReportingFacilityId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeReportingFacilityId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeReportingFacilityId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeReportingFacilityId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeReportingFacilityId

/-- Stop Stock Indicator: one byte code -/
def StopStockIndicator.codes : List UInt8 :=
  [0x30, 0x31]

inductive StopStockIndicator where
  | stopStockNotApplicable -- Stop Stock Not Applicable
  | stopStock -- Stop Stock
  | unlisted (byte : { byte : UInt8 // byte ∉ StopStockIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StopStockIndicator

def toByte : StopStockIndicator → UInt8
  | .stopStockNotApplicable => 0x30
  | .stopStock => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StopStockIndicator :=
  if byte = 0x30 then .stopStockNotApplicable
  else .stopStock

def ofByte (byte : UInt8) : StopStockIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StopStockIndicator) : ofByte value.toByte = value := by
  cases value with
  | stopStockNotApplicable => decide
  | stopStock => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StopStockIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StopStockIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StopStockIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StopStockIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StopStockIndicator

/-- Trade Through Exempt Indicator: one byte code -/
def TradeThroughExemptIndicator.codes : List UInt8 :=
  [0x30, 0x31]

inductive TradeThroughExemptIndicator where
  | notATradeThroughExemption -- Not A Trade Through Exemption
  | tradeThroughExemption -- Trade Through Exemption
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeThroughExemptIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeThroughExemptIndicator

def toByte : TradeThroughExemptIndicator → UInt8
  | .notATradeThroughExemption => 0x30
  | .tradeThroughExemption => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeThroughExemptIndicator :=
  if byte = 0x30 then .notATradeThroughExemption
  else .tradeThroughExemption

def ofByte (byte : UInt8) : TradeThroughExemptIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeThroughExemptIndicator) : ofByte value.toByte = value := by
  cases value with
  | notATradeThroughExemption => decide
  | tradeThroughExemption => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeThroughExemptIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeThroughExemptIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeThroughExemptIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeThroughExemptIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeThroughExemptIndicator

/-- Short Sale Restriction Indicator: one byte code -/
def ShortSaleRestrictionIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x43, 0x44, 0x45]

inductive ShortSaleRestrictionIndicator where
  | shortSaleRestrictionNotApplicable -- Short Sale Restriction Not Applicable
  | shortSaleRestrictionActivated -- Short Sale Restriction Activated
  | shortSaleRestrictionContinued -- Short Sale Restriction Continued
  | shortSaleRestrictionDeactivated -- Short Sale Restriction Deactivated
  | shortSaleRestrictionInEffect -- Short Sale Restriction In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSaleRestrictionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSaleRestrictionIndicator

def toByte : ShortSaleRestrictionIndicator → UInt8
  | .shortSaleRestrictionNotApplicable => 0x20
  | .shortSaleRestrictionActivated => 0x41
  | .shortSaleRestrictionContinued => 0x43
  | .shortSaleRestrictionDeactivated => 0x44
  | .shortSaleRestrictionInEffect => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSaleRestrictionIndicator :=
  if byte = 0x20 then .shortSaleRestrictionNotApplicable
  else if byte = 0x41 then .shortSaleRestrictionActivated
  else if byte = 0x43 then .shortSaleRestrictionContinued
  else if byte = 0x44 then .shortSaleRestrictionDeactivated
  else .shortSaleRestrictionInEffect

def ofByte (byte : UInt8) : ShortSaleRestrictionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSaleRestrictionIndicator) : ofByte value.toByte = value := by
  cases value with
  | shortSaleRestrictionNotApplicable => decide
  | shortSaleRestrictionActivated => decide
  | shortSaleRestrictionContinued => decide
  | shortSaleRestrictionDeactivated => decide
  | shortSaleRestrictionInEffect => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSaleRestrictionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSaleRestrictionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSaleRestrictionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ShortSaleRestrictionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSaleRestrictionIndicator

/-- Cancel Error Action: one byte code -/
def CancelErrorAction.codes : List UInt8 :=
  [0x31, 0x32]

inductive CancelErrorAction where
  | cancel -- Cancel
  | error -- Error
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelErrorAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelErrorAction

def toByte : CancelErrorAction → UInt8
  | .cancel => 0x31
  | .error => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelErrorAction :=
  if byte = 0x31 then .cancel
  else .error

def ofByte (byte : UInt8) : CancelErrorAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelErrorAction) : ofByte value.toByte = value := by
  cases value with
  | cancel => decide
  | error => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelErrorAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelErrorAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelErrorAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CancelErrorAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelErrorAction

/-- Security Status: one byte code -/
def SecurityStatus.codes : List UInt8 :=
  [0x20, 0x32, 0x33, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x43, 0x44, 0x45, 0x46]

inductive SecurityStatus where
  | securityStatusNotApplicable -- Security Status Not Applicable
  | tradingHalt -- Trading Halt
  | resume -- Resume
  | priceIndication -- Price Indication
  | tradingRangeIndication -- Trading Range Indication
  | marketImbalanceBuy -- Market Imbalance Buy
  | marketImbalanceSell -- Market Imbalance Sell
  | closingImbalanceBuy -- Closing Imbalance Buy
  | closingImbalanceSell -- Closing Imbalance Sell
  | noMarketImbalance -- No Market Imbalance
  | noClosingImbalance -- No Closing Imbalance
  | shortSaleRestriction -- Short Sale Restriction
  | limitUpLimitDownLuldReferencePrice -- Limit Up Limit Down Luld Reference Price
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatus

def toByte : SecurityStatus → UInt8
  | .securityStatusNotApplicable => 0x20
  | .tradingHalt => 0x32
  | .resume => 0x33
  | .priceIndication => 0x35
  | .tradingRangeIndication => 0x36
  | .marketImbalanceBuy => 0x37
  | .marketImbalanceSell => 0x38
  | .closingImbalanceBuy => 0x39
  | .closingImbalanceSell => 0x41
  | .noMarketImbalance => 0x43
  | .noClosingImbalance => 0x44
  | .shortSaleRestriction => 0x45
  | .limitUpLimitDownLuldReferencePrice => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x20 then .securityStatusNotApplicable
  else if byte = 0x32 then .tradingHalt
  else if byte = 0x33 then .resume
  else if byte = 0x35 then .priceIndication
  else if byte = 0x36 then .tradingRangeIndication
  else if byte = 0x37 then .marketImbalanceBuy
  else if byte = 0x38 then .marketImbalanceSell
  else if byte = 0x39 then .closingImbalanceBuy
  else if byte = 0x41 then .closingImbalanceSell
  else if byte = 0x43 then .noMarketImbalance
  else if byte = 0x44 then .noClosingImbalance
  else if byte = 0x45 then .shortSaleRestriction
  else .limitUpLimitDownLuldReferencePrice

def ofByte (byte : UInt8) : SecurityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatus) : ofByte value.toByte = value := by
  cases value with
  | securityStatusNotApplicable => decide
  | tradingHalt => decide
  | resume => decide
  | priceIndication => decide
  | tradingRangeIndication => decide
  | marketImbalanceBuy => decide
  | marketImbalanceSell => decide
  | closingImbalanceBuy => decide
  | closingImbalanceSell => decide
  | noMarketImbalance => decide
  | noClosingImbalance => decide
  | shortSaleRestriction => decide
  | limitUpLimitDownLuldReferencePrice => decide
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

/-- Halt Reason: one byte code -/
def HaltReason.codes : List UInt8 :=
  [0x20, 0x41, 0x43, 0x44, 0x45, 0x46, 0x49, 0x4D, 0x4E, 0x4F, 0x50, 0x56, 0x58, 0x59, 0x31, 0x32, 0x33]

inductive HaltReason where
  | haltReasonNotApplicable -- Halt Reason Not Applicable
  | additionalInformationRequested -- Additional Information Requested
  | regulatoryConcern -- Regulatory Concern
  | newsReleased -- News Released
  | mergerEffective -- Merger Effective
  | etfComponentPricesNotAvailable -- Etf Component Prices Not Available
  | orderImbalance -- Order Imbalance
  | limitUpLimitDownLuldTradingPause -- Limit Up Limit Down Luld Trading Pause
  | corporateAction -- Corporate Action
  | newSecurityOffering -- New Security Offering
  | newsPending -- News Pending
  | intradayIndicativeValueNotAvailable -- Intraday Indicative Value Not Available
  | operational -- Operational
  | subPennyTrading -- Sub Penny Trading
  | marketWideCircuitBreakerLevel1Breached -- Market Wide Circuit Breaker Level 1 Breached
  | marketWideCircuitBreakerLevel2Breached -- Market Wide Circuit Breaker Level 2 Breached
  | marketWideCircuitBreakerLevel3Breached -- Market Wide Circuit Breaker Level 3 Breached
  | unlisted (byte : { byte : UInt8 // byte ∉ HaltReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HaltReason

def toByte : HaltReason → UInt8
  | .haltReasonNotApplicable => 0x20
  | .additionalInformationRequested => 0x41
  | .regulatoryConcern => 0x43
  | .newsReleased => 0x44
  | .mergerEffective => 0x45
  | .etfComponentPricesNotAvailable => 0x46
  | .orderImbalance => 0x49
  | .limitUpLimitDownLuldTradingPause => 0x4D
  | .corporateAction => 0x4E
  | .newSecurityOffering => 0x4F
  | .newsPending => 0x50
  | .intradayIndicativeValueNotAvailable => 0x56
  | .operational => 0x58
  | .subPennyTrading => 0x59
  | .marketWideCircuitBreakerLevel1Breached => 0x31
  | .marketWideCircuitBreakerLevel2Breached => 0x32
  | .marketWideCircuitBreakerLevel3Breached => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HaltReason :=
  if byte = 0x20 then .haltReasonNotApplicable
  else if byte = 0x41 then .additionalInformationRequested
  else if byte = 0x43 then .regulatoryConcern
  else if byte = 0x44 then .newsReleased
  else if byte = 0x45 then .mergerEffective
  else if byte = 0x46 then .etfComponentPricesNotAvailable
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x4D then .limitUpLimitDownLuldTradingPause
  else if byte = 0x4E then .corporateAction
  else if byte = 0x4F then .newSecurityOffering
  else if byte = 0x50 then .newsPending
  else if byte = 0x56 then .intradayIndicativeValueNotAvailable
  else if byte = 0x58 then .operational
  else if byte = 0x59 then .subPennyTrading
  else if byte = 0x31 then .marketWideCircuitBreakerLevel1Breached
  else if byte = 0x32 then .marketWideCircuitBreakerLevel2Breached
  else .marketWideCircuitBreakerLevel3Breached

def ofByte (byte : UInt8) : HaltReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HaltReason) : ofByte value.toByte = value := by
  cases value with
  | haltReasonNotApplicable => decide
  | additionalInformationRequested => decide
  | regulatoryConcern => decide
  | newsReleased => decide
  | mergerEffective => decide
  | etfComponentPricesNotAvailable => decide
  | orderImbalance => decide
  | limitUpLimitDownLuldTradingPause => decide
  | corporateAction => decide
  | newSecurityOffering => decide
  | newsPending => decide
  | intradayIndicativeValueNotAvailable => decide
  | operational => decide
  | subPennyTrading => decide
  | marketWideCircuitBreakerLevel1Breached => decide
  | marketWideCircuitBreakerLevel2Breached => decide
  | marketWideCircuitBreakerLevel3Breached => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HaltReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HaltReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HaltReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : HaltReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HaltReason

/-- Sale Condition Category: one byte code -/
def SaleConditionCategory.codes : List UInt8 :=
  [0x20, 0x31, 0x32, 0x33, 0x34]

inductive SaleConditionCategory where
  | saleConditionCategoryNotApplicable -- Sale Condition Category Not Applicable
  | saleConditionCategory1 -- Sale Condition Category 1
  | saleConditionCategory2 -- Sale Condition Category 2
  | saleConditionCategory3 -- Sale Condition Category 3
  | saleConditionCategory4 -- Sale Condition Category 4
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleConditionCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleConditionCategory

def toByte : SaleConditionCategory → UInt8
  | .saleConditionCategoryNotApplicable => 0x20
  | .saleConditionCategory1 => 0x31
  | .saleConditionCategory2 => 0x32
  | .saleConditionCategory3 => 0x33
  | .saleConditionCategory4 => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleConditionCategory :=
  if byte = 0x20 then .saleConditionCategoryNotApplicable
  else if byte = 0x31 then .saleConditionCategory1
  else if byte = 0x32 then .saleConditionCategory2
  else if byte = 0x33 then .saleConditionCategory3
  else .saleConditionCategory4

def ofByte (byte : UInt8) : SaleConditionCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleConditionCategory) : ofByte value.toByte = value := by
  cases value with
  | saleConditionCategoryNotApplicable => decide
  | saleConditionCategory1 => decide
  | saleConditionCategory2 => decide
  | saleConditionCategory3 => decide
  | saleConditionCategory4 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleConditionCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleConditionCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleConditionCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SaleConditionCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleConditionCategory

/-- Timestamp 1: 8 bytes -/
structure Timestamp1 where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace Timestamp1

def encode (message : Timestamp1) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (Timestamp1 × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : Timestamp1) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : Timestamp1) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Timestamp1) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Timestamp1

/-- Rejection Message: 14 bytes -/
structure RejectionMessage where
  errorCode : BitVec 8
  blockSequenceNumber : BitVec 32
  participantReferenceNumber : BitVec 64
  messageId : BitVec 8
  deriving DecidableEq, Repr

namespace RejectionMessage

def encode (message : RejectionMessage) : List UInt8 :=
  encodeUInt 1 message.errorCode
    ++ (encodeUInt 4 message.blockSequenceNumber
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (encodeUInt 1 message.messageId)))

def decode (bytes : List UInt8) : Option (RejectionMessage × List UInt8) := do
  let (errorCode, bytes) ← decodeUInt 1 bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  pure ({ errorCode, blockSequenceNumber, participantReferenceNumber, messageId }, bytes)

@[simp] theorem encode_length (message : RejectionMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : RejectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RejectionMessage

/-- Warning Message: 12 bytes -/
structure WarningMessage where
  previousBlockSequenceNumber : BitVec 32
  previousParticipantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace WarningMessage

def encode (message : WarningMessage) : List UInt8 :=
  encodeUInt 4 message.previousBlockSequenceNumber
    ++ (encodeUInt 8 message.previousParticipantReferenceNumber)

def decode (bytes : List UInt8) : Option (WarningMessage × List UInt8) := do
  let (previousBlockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (previousParticipantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ previousBlockSequenceNumber, previousParticipantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : WarningMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : WarningMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WarningMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end WarningMessage

/-- Any Administrative Message Payload, selected by Administrative Message Type -/
inductive AdministrativeMessagePayload where
  | rejectionMessage (message : RejectionMessage) -- "R" 0x52
  | warningMessage (message : WarningMessage) -- "W" 0x57
  deriving DecidableEq, Repr

namespace AdministrativeMessagePayload

/-- The Administrative Message Type each message is sent under -/
def tag : AdministrativeMessagePayload → BitVec 8
  | .rejectionMessage _ => 82
  | .warningMessage _ => 87

def encode : AdministrativeMessagePayload → List UInt8
  | .rejectionMessage message => RejectionMessage.encode message
  | .warningMessage message => WarningMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AdministrativeMessagePayload) : (encode message).length ≤ 14 := by
  cases message with
  | rejectionMessage inner =>
    simp only [encode, RejectionMessage.encode_length]
    omega
  | warningMessage inner =>
    simp only [encode, WarningMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AdministrativeMessagePayload × List UInt8) :=
  if tag = 82 then (RejectionMessage.decode bytes).map fun (message, rest) => (.rejectionMessage message, rest)
  else if tag = 87 then (WarningMessage.decode bytes).map fun (message, rest) => (.warningMessage message, rest)
  else none

@[simp] theorem decode_encode (message : AdministrativeMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end AdministrativeMessagePayload

/-- Administrative Message -/
structure AdministrativeMessage where
  administrativeMessagePayload : AdministrativeMessagePayload
  deriving DecidableEq, Repr

namespace AdministrativeMessage

def encode (message : AdministrativeMessage) : List UInt8 :=
  encodeUInt 1 (AdministrativeMessagePayload.tag message.administrativeMessagePayload)
    ++ (AdministrativeMessagePayload.encode message.administrativeMessagePayload)

def decode (bytes : List UInt8) : Option (AdministrativeMessage × List UInt8) := do
  let (administrativeMessageType, bytes) ← decodeUInt 1 bytes
  let (administrativeMessagePayload, bytes) ← AdministrativeMessagePayload.decode administrativeMessageType bytes
  pure ({ administrativeMessagePayload }, bytes)

theorem encode_length_pos (message : AdministrativeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AdministrativeMessage) : (encode message).length ≤ 15 := by
  unfold encode
  cases message.administrativeMessagePayload with
  | rejectionMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, RejectionMessage.encode_length]
    omega
  | warningMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, WarningMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : AdministrativeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [AdministrativeMessagePayload.decode_encode, some_bind]
  rfl

end AdministrativeMessage

/-- Start Of Day Message: 0 bytes -/
structure StartOfDayMessage where
  deriving DecidableEq, Repr

namespace StartOfDayMessage

def encode (_ : StartOfDayMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (StartOfDayMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : StartOfDayMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : StartOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end StartOfDayMessage

/-- Sequence Information And Message Count Inquiry Message: 0 bytes -/
structure SequenceInformationAndMessageCountInquiryMessage where
  deriving DecidableEq, Repr

namespace SequenceInformationAndMessageCountInquiryMessage

def encode (_ : SequenceInformationAndMessageCountInquiryMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SequenceInformationAndMessageCountInquiryMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SequenceInformationAndMessageCountInquiryMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SequenceInformationAndMessageCountInquiryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end SequenceInformationAndMessageCountInquiryMessage

/-- Sequence Information And Message Count Response Message: 20 bytes -/
structure SequenceInformationAndMessageCountResponseMessage where
  currentBlockSequenceNumber : BitVec 32
  lastParticipantReferenceNumber : BitVec 64
  messageCount : BitVec 64
  deriving DecidableEq, Repr

namespace SequenceInformationAndMessageCountResponseMessage

def encode (message : SequenceInformationAndMessageCountResponseMessage) : List UInt8 :=
  encodeUInt 4 message.currentBlockSequenceNumber
    ++ (encodeUInt 8 message.lastParticipantReferenceNumber
    ++ (encodeUInt 8 message.messageCount))

def decode (bytes : List UInt8) : Option (SequenceInformationAndMessageCountResponseMessage × List UInt8) := do
  let (currentBlockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (lastParticipantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 8 bytes
  pure ({ currentBlockSequenceNumber, lastParticipantReferenceNumber, messageCount }, bytes)

@[simp] theorem encode_length (message : SequenceInformationAndMessageCountResponseMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SequenceInformationAndMessageCountResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceInformationAndMessageCountResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SequenceInformationAndMessageCountResponseMessage

/-- Line Integrity Message: 0 bytes -/
structure LineIntegrityMessage where
  deriving DecidableEq, Repr

namespace LineIntegrityMessage

def encode (_ : LineIntegrityMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LineIntegrityMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LineIntegrityMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LineIntegrityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LineIntegrityMessage

/-- End Of Day Message: 0 bytes -/
structure EndOfDayMessage where
  deriving DecidableEq, Repr

namespace EndOfDayMessage

def encode (_ : EndOfDayMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfDayMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfDayMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end EndOfDayMessage

/-- Test Message: 256 bytes -/
structure TestMessage where
  data : Alpha 256
  deriving DecidableEq, Repr

namespace TestMessage

def encode (message : TestMessage) : List UInt8 :=
  Alpha.encode message.data

def decode (bytes : List UInt8) : Option (TestMessage × List UInt8) := do
  let (data, bytes) ← Alpha.decode 256 bytes
  pure ({ data }, bytes)

@[simp] theorem encode_length (message : TestMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : TestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end TestMessage

/-- Any Control Message Payload, selected by Control Message Type -/
inductive ControlMessagePayload where
  | startOfDayMessage (message : StartOfDayMessage) -- "A" 0x41
  | sequenceInformationAndMessageCountInquiryMessage (message : SequenceInformationAndMessageCountInquiryMessage) -- "I" 0x49
  | sequenceInformationAndMessageCountResponseMessage (message : SequenceInformationAndMessageCountResponseMessage) -- "N" 0x4E
  | lineIntegrityMessage (message : LineIntegrityMessage) -- "T" 0x54
  | endOfDayMessage (message : EndOfDayMessage) -- "Z" 0x5A
  | testMessage (message : TestMessage) -- "5" 0x35
  deriving DecidableEq, Repr

namespace ControlMessagePayload

/-- The Control Message Type each message is sent under -/
def tag : ControlMessagePayload → BitVec 8
  | .startOfDayMessage _ => 65
  | .sequenceInformationAndMessageCountInquiryMessage _ => 73
  | .sequenceInformationAndMessageCountResponseMessage _ => 78
  | .lineIntegrityMessage _ => 84
  | .endOfDayMessage _ => 90
  | .testMessage _ => 53

def encode : ControlMessagePayload → List UInt8
  | .startOfDayMessage message => StartOfDayMessage.encode message
  | .sequenceInformationAndMessageCountInquiryMessage message => SequenceInformationAndMessageCountInquiryMessage.encode message
  | .sequenceInformationAndMessageCountResponseMessage message => SequenceInformationAndMessageCountResponseMessage.encode message
  | .lineIntegrityMessage message => LineIntegrityMessage.encode message
  | .endOfDayMessage message => EndOfDayMessage.encode message
  | .testMessage message => TestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ControlMessagePayload) : (encode message).length ≤ 256 := by
  cases message with
  | startOfDayMessage inner =>
    simp only [encode, StartOfDayMessage.encode_length]
    omega
  | sequenceInformationAndMessageCountInquiryMessage inner =>
    simp only [encode, SequenceInformationAndMessageCountInquiryMessage.encode_length]
    omega
  | sequenceInformationAndMessageCountResponseMessage inner =>
    simp only [encode, SequenceInformationAndMessageCountResponseMessage.encode_length]
    omega
  | lineIntegrityMessage inner =>
    simp only [encode, LineIntegrityMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [encode, EndOfDayMessage.encode_length]
    omega
  | testMessage inner =>
    simp only [encode, TestMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ControlMessagePayload × List UInt8) :=
  if tag = 65 then (StartOfDayMessage.decode bytes).map fun (message, rest) => (.startOfDayMessage message, rest)
  else if tag = 73 then (SequenceInformationAndMessageCountInquiryMessage.decode bytes).map fun (message, rest) => (.sequenceInformationAndMessageCountInquiryMessage message, rest)
  else if tag = 78 then (SequenceInformationAndMessageCountResponseMessage.decode bytes).map fun (message, rest) => (.sequenceInformationAndMessageCountResponseMessage message, rest)
  else if tag = 84 then (LineIntegrityMessage.decode bytes).map fun (message, rest) => (.lineIntegrityMessage message, rest)
  else if tag = 90 then (EndOfDayMessage.decode bytes).map fun (message, rest) => (.endOfDayMessage message, rest)
  else if tag = 53 then (TestMessage.decode bytes).map fun (message, rest) => (.testMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ControlMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ControlMessagePayload

/-- Control Message -/
structure ControlMessage where
  controlMessagePayload : ControlMessagePayload
  deriving DecidableEq, Repr

namespace ControlMessage

def encode (message : ControlMessage) : List UInt8 :=
  encodeUInt 1 (ControlMessagePayload.tag message.controlMessagePayload)
    ++ (ControlMessagePayload.encode message.controlMessagePayload)

def decode (bytes : List UInt8) : Option (ControlMessage × List UInt8) := do
  let (controlMessageType, bytes) ← decodeUInt 1 bytes
  let (controlMessagePayload, bytes) ← ControlMessagePayload.decode controlMessageType bytes
  pure ({ controlMessagePayload }, bytes)

theorem encode_length_pos (message : ControlMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ControlMessage) : (encode message).length ≤ 257 := by
  unfold encode
  cases message.controlMessagePayload with
  | startOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, StartOfDayMessage.encode_length]
    omega
  | sequenceInformationAndMessageCountInquiryMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, SequenceInformationAndMessageCountInquiryMessage.encode_length]
    omega
  | sequenceInformationAndMessageCountResponseMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, SequenceInformationAndMessageCountResponseMessage.encode_length]
    omega
  | lineIntegrityMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, LineIntegrityMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, EndOfDayMessage.encode_length]
    omega
  | testMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, TestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ControlMessagePayload.decode_encode, some_bind]
  rfl

end ControlMessage

/-- Index Message: 19 bytes -/
structure IndexMessage where
  indexSymbol : Alpha 11
  indexValue : BitVec 64
  deriving DecidableEq, Repr

namespace IndexMessage

def encode (message : IndexMessage) : List UInt8 :=
  Alpha.encode message.indexSymbol
    ++ (encodeUInt 8 message.indexValue)

def decode (bytes : List UInt8) : Option (IndexMessage × List UInt8) := do
  let (indexSymbol, bytes) ← Alpha.decode 11 bytes
  let (indexValue, bytes) ← decodeUInt 8 bytes
  pure ({ indexSymbol, indexValue }, bytes)

@[simp] theorem encode_length (message : IndexMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : IndexMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndexMessage

/-- Bid And Offer Index Message: 27 bytes -/
structure BidAndOfferIndexMessage where
  indexSymbol : Alpha 11
  bidIndexValue : BitVec 64
  offerIndexValue : BitVec 64
  deriving DecidableEq, Repr

namespace BidAndOfferIndexMessage

def encode (message : BidAndOfferIndexMessage) : List UInt8 :=
  Alpha.encode message.indexSymbol
    ++ (encodeUInt 8 message.bidIndexValue
    ++ (encodeUInt 8 message.offerIndexValue))

def decode (bytes : List UInt8) : Option (BidAndOfferIndexMessage × List UInt8) := do
  let (indexSymbol, bytes) ← Alpha.decode 11 bytes
  let (bidIndexValue, bytes) ← decodeUInt 8 bytes
  let (offerIndexValue, bytes) ← decodeUInt 8 bytes
  pure ({ indexSymbol, bidIndexValue, offerIndexValue }, bytes)

@[simp] theorem encode_length (message : BidAndOfferIndexMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BidAndOfferIndexMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidAndOfferIndexMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidAndOfferIndexMessage

/-- Any Indices Message Payload, selected by Indices Message Type -/
inductive IndicesMessagePayload where
  | indexMessage (message : IndexMessage) -- "I" 0x49
  | bidAndOfferIndexMessage (message : BidAndOfferIndexMessage) -- "Q" 0x51
  deriving DecidableEq, Repr

namespace IndicesMessagePayload

/-- The Indices Message Type each message is sent under -/
def tag : IndicesMessagePayload → BitVec 8
  | .indexMessage _ => 73
  | .bidAndOfferIndexMessage _ => 81

def encode : IndicesMessagePayload → List UInt8
  | .indexMessage message => IndexMessage.encode message
  | .bidAndOfferIndexMessage message => BidAndOfferIndexMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : IndicesMessagePayload) : (encode message).length ≤ 27 := by
  cases message with
  | indexMessage inner =>
    simp only [encode, IndexMessage.encode_length]
    omega
  | bidAndOfferIndexMessage inner =>
    simp only [encode, BidAndOfferIndexMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (IndicesMessagePayload × List UInt8) :=
  if tag = 73 then (IndexMessage.decode bytes).map fun (message, rest) => (.indexMessage message, rest)
  else if tag = 81 then (BidAndOfferIndexMessage.decode bytes).map fun (message, rest) => (.bidAndOfferIndexMessage message, rest)
  else none

@[simp] theorem decode_encode (message : IndicesMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end IndicesMessagePayload

/-- Indices Message -/
structure IndicesMessage where
  indicesMessagePayload : IndicesMessagePayload
  deriving DecidableEq, Repr

namespace IndicesMessage

def encode (message : IndicesMessage) : List UInt8 :=
  encodeUInt 1 (IndicesMessagePayload.tag message.indicesMessagePayload)
    ++ (IndicesMessagePayload.encode message.indicesMessagePayload)

def decode (bytes : List UInt8) : Option (IndicesMessage × List UInt8) := do
  let (indicesMessageType, bytes) ← decodeUInt 1 bytes
  let (indicesMessagePayload, bytes) ← IndicesMessagePayload.decode indicesMessageType bytes
  pure ({ indicesMessagePayload }, bytes)

theorem encode_length_pos (message : IndicesMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IndicesMessage) : (encode message).length ≤ 28 := by
  unfold encode
  cases message.indicesMessagePayload with
  | indexMessage inner =>
    simp only [IndicesMessagePayload.encode, List.length_append, encodeUInt_length, IndexMessage.encode_length]
    omega
  | bidAndOfferIndexMessage inner =>
    simp only [IndicesMessagePayload.encode, List.length_append, encodeUInt_length, BidAndOfferIndexMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : IndicesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [IndicesMessagePayload.decode_encode, some_bind]
  rfl

end IndicesMessage

/-- Approximate Trades And Total Dollar Value Message: 12 bytes -/
structure ApproximateTradesAndTotalDollarValueMessage where
  totalTrades : BitVec 32
  dollarValue : BitVec 64
  deriving DecidableEq, Repr

namespace ApproximateTradesAndTotalDollarValueMessage

def encode (message : ApproximateTradesAndTotalDollarValueMessage) : List UInt8 :=
  encodeUInt 4 message.totalTrades
    ++ (encodeUInt 8 message.dollarValue)

def decode (bytes : List UInt8) : Option (ApproximateTradesAndTotalDollarValueMessage × List UInt8) := do
  let (totalTrades, bytes) ← decodeUInt 4 bytes
  let (dollarValue, bytes) ← decodeUInt 8 bytes
  pure ({ totalTrades, dollarValue }, bytes)

@[simp] theorem encode_length (message : ApproximateTradesAndTotalDollarValueMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ApproximateTradesAndTotalDollarValueMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ApproximateTradesAndTotalDollarValueMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ApproximateTradesAndTotalDollarValueMessage

/-- Crossing Session Message: 24 bytes -/
structure CrossingSessionMessage where
  crossingSessionITotalTradesVolume : BitVec 64
  crossingSessionIiDollarValue : BitVec 64
  crossingSessionIiTotalTradesVolume : BitVec 64
  deriving DecidableEq, Repr

namespace CrossingSessionMessage

def encode (message : CrossingSessionMessage) : List UInt8 :=
  encodeUInt 8 message.crossingSessionITotalTradesVolume
    ++ (encodeUInt 8 message.crossingSessionIiDollarValue
    ++ (encodeUInt 8 message.crossingSessionIiTotalTradesVolume))

def decode (bytes : List UInt8) : Option (CrossingSessionMessage × List UInt8) := do
  let (crossingSessionITotalTradesVolume, bytes) ← decodeUInt 8 bytes
  let (crossingSessionIiDollarValue, bytes) ← decodeUInt 8 bytes
  let (crossingSessionIiTotalTradesVolume, bytes) ← decodeUInt 8 bytes
  pure ({ crossingSessionITotalTradesVolume, crossingSessionIiDollarValue, crossingSessionIiTotalTradesVolume }, bytes)

@[simp] theorem encode_length (message : CrossingSessionMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : CrossingSessionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossingSessionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CrossingSessionMessage

/-- Any Market Status Message Payload, selected by Market Status Message Type -/
inductive MarketStatusMessagePayload where
  | approximateTradesAndTotalDollarValueMessage (message : ApproximateTradesAndTotalDollarValueMessage) -- "O" 0x4F
  | crossingSessionMessage (message : CrossingSessionMessage) -- "P" 0x50
  deriving DecidableEq, Repr

namespace MarketStatusMessagePayload

/-- The Market Status Message Type each message is sent under -/
def tag : MarketStatusMessagePayload → BitVec 8
  | .approximateTradesAndTotalDollarValueMessage _ => 79
  | .crossingSessionMessage _ => 80

def encode : MarketStatusMessagePayload → List UInt8
  | .approximateTradesAndTotalDollarValueMessage message => ApproximateTradesAndTotalDollarValueMessage.encode message
  | .crossingSessionMessage message => CrossingSessionMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MarketStatusMessagePayload) : (encode message).length ≤ 24 := by
  cases message with
  | approximateTradesAndTotalDollarValueMessage inner =>
    simp only [encode, ApproximateTradesAndTotalDollarValueMessage.encode_length]
    omega
  | crossingSessionMessage inner =>
    simp only [encode, CrossingSessionMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (MarketStatusMessagePayload × List UInt8) :=
  if tag = 79 then (ApproximateTradesAndTotalDollarValueMessage.decode bytes).map fun (message, rest) => (.approximateTradesAndTotalDollarValueMessage message, rest)
  else if tag = 80 then (CrossingSessionMessage.decode bytes).map fun (message, rest) => (.crossingSessionMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MarketStatusMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MarketStatusMessagePayload

/-- Market Status Message -/
structure MarketStatusMessage where
  marketStatusMessagePayload : MarketStatusMessagePayload
  deriving DecidableEq, Repr

namespace MarketStatusMessage

def encode (message : MarketStatusMessage) : List UInt8 :=
  encodeUInt 1 (MarketStatusMessagePayload.tag message.marketStatusMessagePayload)
    ++ (MarketStatusMessagePayload.encode message.marketStatusMessagePayload)

def decode (bytes : List UInt8) : Option (MarketStatusMessage × List UInt8) := do
  let (marketStatusMessageType, bytes) ← decodeUInt 1 bytes
  let (marketStatusMessagePayload, bytes) ← MarketStatusMessagePayload.decode marketStatusMessageType bytes
  pure ({ marketStatusMessagePayload }, bytes)

theorem encode_length_pos (message : MarketStatusMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketStatusMessage) : (encode message).length ≤ 25 := by
  unfold encode
  cases message.marketStatusMessagePayload with
  | approximateTradesAndTotalDollarValueMessage inner =>
    simp only [MarketStatusMessagePayload.encode, List.length_append, encodeUInt_length, ApproximateTradesAndTotalDollarValueMessage.encode_length]
    omega
  | crossingSessionMessage inner =>
    simp only [MarketStatusMessagePayload.encode, List.length_append, encodeUInt_length, CrossingSessionMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : MarketStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MarketStatusMessagePayload.decode_encode, some_bind]
  rfl

end MarketStatusMessage

/-- Corrected Prior Day Trade Date And Time: 8 bytes -/
structure CorrectedPriorDayTradeDateAndTime where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace CorrectedPriorDayTradeDateAndTime

def encode (message : CorrectedPriorDayTradeDateAndTime) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (CorrectedPriorDayTradeDateAndTime × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : CorrectedPriorDayTradeDateAndTime) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : CorrectedPriorDayTradeDateAndTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CorrectedPriorDayTradeDateAndTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CorrectedPriorDayTradeDateAndTime

/-- Original Prior Day Trade Date And Time: 8 bytes -/
structure OriginalPriorDayTradeDateAndTime where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace OriginalPriorDayTradeDateAndTime

def encode (message : OriginalPriorDayTradeDateAndTime) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (OriginalPriorDayTradeDateAndTime × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : OriginalPriorDayTradeDateAndTime) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OriginalPriorDayTradeDateAndTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OriginalPriorDayTradeDateAndTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OriginalPriorDayTradeDateAndTime

/-- Prior Day Trade Correction Message: 69 bytes -/
structure PriorDayTradeCorrectionMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  correctedSaleCondition : Alpha 4
  correctedTradePrice : BitVec 64
  correctedTradeVolume : BitVec 32
  correctedSellersSaleDays : BitVec 8
  correctedStopStockIndicator : Alpha 1
  correctedTradeThroughExemptIndicator : Alpha 1
  correctedShortSaleRestrictionIndicator : Alpha 1
  correctedPriorDayTradeDateAndTime : CorrectedPriorDayTradeDateAndTime
  tradeReportingFacilityId : TradeReportingFacilityId
  originalSaleCondition : Alpha 4
  originalTradePrice : BitVec 64
  originalTradeVolume : BitVec 32
  originalSellersSaleDays : BitVec 8
  originalStopStockIndicator : Alpha 1
  originalTradeThroughExemptIndicator : Alpha 1
  originalShortSaleRestrictionIndicator : Alpha 1
  originalPriorDayTradeDateAndTime : OriginalPriorDayTradeDateAndTime
  deriving DecidableEq, Repr

namespace PriorDayTradeCorrectionMessage

def encode (message : PriorDayTradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.correctedSaleCondition
    ++ (encodeUInt 8 message.correctedTradePrice
    ++ (encodeUInt 4 message.correctedTradeVolume
    ++ (encodeUInt 1 message.correctedSellersSaleDays
    ++ (Alpha.encode message.correctedStopStockIndicator
    ++ (Alpha.encode message.correctedTradeThroughExemptIndicator
    ++ (Alpha.encode message.correctedShortSaleRestrictionIndicator
    ++ (CorrectedPriorDayTradeDateAndTime.encode message.correctedPriorDayTradeDateAndTime
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (Alpha.encode message.originalSaleCondition
    ++ (encodeUInt 8 message.originalTradePrice
    ++ (encodeUInt 4 message.originalTradeVolume
    ++ (encodeUInt 1 message.originalSellersSaleDays
    ++ (Alpha.encode message.originalStopStockIndicator
    ++ (Alpha.encode message.originalTradeThroughExemptIndicator
    ++ (Alpha.encode message.originalShortSaleRestrictionIndicator
    ++ (OriginalPriorDayTradeDateAndTime.encode message.originalPriorDayTradeDateAndTime))))))))))))))))))

def decode (bytes : List UInt8) : Option (PriorDayTradeCorrectionMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (correctedSaleCondition, bytes) ← Alpha.decode 4 bytes
  let (correctedTradePrice, bytes) ← decodeUInt 8 bytes
  let (correctedTradeVolume, bytes) ← decodeUInt 4 bytes
  let (correctedSellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (correctedStopStockIndicator, bytes) ← Alpha.decode 1 bytes
  let (correctedTradeThroughExemptIndicator, bytes) ← Alpha.decode 1 bytes
  let (correctedShortSaleRestrictionIndicator, bytes) ← Alpha.decode 1 bytes
  let (correctedPriorDayTradeDateAndTime, bytes) ← CorrectedPriorDayTradeDateAndTime.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (originalSaleCondition, bytes) ← Alpha.decode 4 bytes
  let (originalTradePrice, bytes) ← decodeUInt 8 bytes
  let (originalTradeVolume, bytes) ← decodeUInt 4 bytes
  let (originalSellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (originalStopStockIndicator, bytes) ← Alpha.decode 1 bytes
  let (originalTradeThroughExemptIndicator, bytes) ← Alpha.decode 1 bytes
  let (originalShortSaleRestrictionIndicator, bytes) ← Alpha.decode 1 bytes
  let (originalPriorDayTradeDateAndTime, bytes) ← OriginalPriorDayTradeDateAndTime.decode bytes
  pure ({ securitySymbol, instrumentType, correctedSaleCondition, correctedTradePrice, correctedTradeVolume, correctedSellersSaleDays, correctedStopStockIndicator, correctedTradeThroughExemptIndicator, correctedShortSaleRestrictionIndicator, correctedPriorDayTradeDateAndTime, tradeReportingFacilityId, originalSaleCondition, originalTradePrice, originalTradeVolume, originalSellersSaleDays, originalStopStockIndicator, originalTradeThroughExemptIndicator, originalShortSaleRestrictionIndicator, originalPriorDayTradeDateAndTime }, bytes)

@[simp] theorem encode_length (message : PriorDayTradeCorrectionMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, CorrectedPriorDayTradeDateAndTime.encode_length, TradeReportingFacilityId.encode_length, OriginalPriorDayTradeDateAndTime.encode_length]

theorem encode_length_pos (message : PriorDayTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriorDayTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedPriorDayTradeDateAndTime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [OriginalPriorDayTradeDateAndTime.decode_encode, some_bind]
  rfl

end PriorDayTradeCorrectionMessage

/-- Fractional Prior Day Trade Correction Message: 77 bytes -/
structure FractionalPriorDayTradeCorrectionMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  correctedSaleCondition : Alpha 4
  correctedTradePrice : BitVec 64
  correctedFractionalTradeVolume : BitVec 64
  correctedSellersSaleDays : BitVec 8
  correctedStopStockIndicator : Alpha 1
  correctedTradeThroughExemptIndicator : Alpha 1
  correctedShortSaleRestrictionIndicator : Alpha 1
  correctedPriorDayTradeDateAndTime : CorrectedPriorDayTradeDateAndTime
  tradeReportingFacilityId : TradeReportingFacilityId
  originalSaleCondition : Alpha 4
  originalTradePrice : BitVec 64
  originalFractionalTradeVolume : BitVec 64
  originalSellersSaleDays : BitVec 8
  originalStopStockIndicator : Alpha 1
  originalTradeThroughExemptIndicator : Alpha 1
  originalShortSaleRestrictionIndicator : Alpha 1
  originalPriorDayTradeDateAndTime : OriginalPriorDayTradeDateAndTime
  deriving DecidableEq, Repr

namespace FractionalPriorDayTradeCorrectionMessage

def encode (message : FractionalPriorDayTradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.correctedSaleCondition
    ++ (encodeUInt 8 message.correctedTradePrice
    ++ (encodeUInt 8 message.correctedFractionalTradeVolume
    ++ (encodeUInt 1 message.correctedSellersSaleDays
    ++ (Alpha.encode message.correctedStopStockIndicator
    ++ (Alpha.encode message.correctedTradeThroughExemptIndicator
    ++ (Alpha.encode message.correctedShortSaleRestrictionIndicator
    ++ (CorrectedPriorDayTradeDateAndTime.encode message.correctedPriorDayTradeDateAndTime
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (Alpha.encode message.originalSaleCondition
    ++ (encodeUInt 8 message.originalTradePrice
    ++ (encodeUInt 8 message.originalFractionalTradeVolume
    ++ (encodeUInt 1 message.originalSellersSaleDays
    ++ (Alpha.encode message.originalStopStockIndicator
    ++ (Alpha.encode message.originalTradeThroughExemptIndicator
    ++ (Alpha.encode message.originalShortSaleRestrictionIndicator
    ++ (OriginalPriorDayTradeDateAndTime.encode message.originalPriorDayTradeDateAndTime))))))))))))))))))

def decode (bytes : List UInt8) : Option (FractionalPriorDayTradeCorrectionMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (correctedSaleCondition, bytes) ← Alpha.decode 4 bytes
  let (correctedTradePrice, bytes) ← decodeUInt 8 bytes
  let (correctedFractionalTradeVolume, bytes) ← decodeUInt 8 bytes
  let (correctedSellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (correctedStopStockIndicator, bytes) ← Alpha.decode 1 bytes
  let (correctedTradeThroughExemptIndicator, bytes) ← Alpha.decode 1 bytes
  let (correctedShortSaleRestrictionIndicator, bytes) ← Alpha.decode 1 bytes
  let (correctedPriorDayTradeDateAndTime, bytes) ← CorrectedPriorDayTradeDateAndTime.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (originalSaleCondition, bytes) ← Alpha.decode 4 bytes
  let (originalTradePrice, bytes) ← decodeUInt 8 bytes
  let (originalFractionalTradeVolume, bytes) ← decodeUInt 8 bytes
  let (originalSellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (originalStopStockIndicator, bytes) ← Alpha.decode 1 bytes
  let (originalTradeThroughExemptIndicator, bytes) ← Alpha.decode 1 bytes
  let (originalShortSaleRestrictionIndicator, bytes) ← Alpha.decode 1 bytes
  let (originalPriorDayTradeDateAndTime, bytes) ← OriginalPriorDayTradeDateAndTime.decode bytes
  pure ({ securitySymbol, instrumentType, correctedSaleCondition, correctedTradePrice, correctedFractionalTradeVolume, correctedSellersSaleDays, correctedStopStockIndicator, correctedTradeThroughExemptIndicator, correctedShortSaleRestrictionIndicator, correctedPriorDayTradeDateAndTime, tradeReportingFacilityId, originalSaleCondition, originalTradePrice, originalFractionalTradeVolume, originalSellersSaleDays, originalStopStockIndicator, originalTradeThroughExemptIndicator, originalShortSaleRestrictionIndicator, originalPriorDayTradeDateAndTime }, bytes)

@[simp] theorem encode_length (message : FractionalPriorDayTradeCorrectionMessage) : (encode message).length = 77 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, CorrectedPriorDayTradeDateAndTime.encode_length, TradeReportingFacilityId.encode_length, OriginalPriorDayTradeDateAndTime.encode_length]

theorem encode_length_pos (message : FractionalPriorDayTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FractionalPriorDayTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedPriorDayTradeDateAndTime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [OriginalPriorDayTradeDateAndTime.decode_encode, some_bind]
  rfl

end FractionalPriorDayTradeCorrectionMessage

/-- Prior Day Trade Date And Time: 8 bytes -/
structure PriorDayTradeDateAndTime where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace PriorDayTradeDateAndTime

def encode (message : PriorDayTradeDateAndTime) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (PriorDayTradeDateAndTime × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : PriorDayTradeDateAndTime) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PriorDayTradeDateAndTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriorDayTradeDateAndTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriorDayTradeDateAndTime

/-- Prior Day Trade Message: 41 bytes -/
structure PriorDayTradeMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  saleCondition : Alpha 4
  tradePrice : BitVec 64
  tradeVolume : BitVec 32
  sellersSaleDays : BitVec 8
  stopStockIndicator : StopStockIndicator
  tradeThroughExemptIndicator : TradeThroughExemptIndicator
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  tradeReportingFacilityId : TradeReportingFacilityId
  priorDayTradeDateAndTime : PriorDayTradeDateAndTime
  deriving DecidableEq, Repr

namespace PriorDayTradeMessage

def encode (message : PriorDayTradeMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.saleCondition
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.tradeVolume
    ++ (encodeUInt 1 message.sellersSaleDays
    ++ (StopStockIndicator.encode message.stopStockIndicator
    ++ (TradeThroughExemptIndicator.encode message.tradeThroughExemptIndicator
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (PriorDayTradeDateAndTime.encode message.priorDayTradeDateAndTime))))))))))

def decode (bytes : List UInt8) : Option (PriorDayTradeMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (saleCondition, bytes) ← Alpha.decode 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeVolume, bytes) ← decodeUInt 4 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (stopStockIndicator, bytes) ← StopStockIndicator.decode bytes
  let (tradeThroughExemptIndicator, bytes) ← TradeThroughExemptIndicator.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (priorDayTradeDateAndTime, bytes) ← PriorDayTradeDateAndTime.decode bytes
  pure ({ securitySymbol, instrumentType, saleCondition, tradePrice, tradeVolume, sellersSaleDays, stopStockIndicator, tradeThroughExemptIndicator, shortSaleRestrictionIndicator, tradeReportingFacilityId, priorDayTradeDateAndTime }, bytes)

@[simp] theorem encode_length (message : PriorDayTradeMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, StopStockIndicator.encode_length, TradeThroughExemptIndicator.encode_length, ShortSaleRestrictionIndicator.encode_length, TradeReportingFacilityId.encode_length, PriorDayTradeDateAndTime.encode_length]

theorem encode_length_pos (message : PriorDayTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriorDayTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StopStockIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [PriorDayTradeDateAndTime.decode_encode, some_bind]
  rfl

end PriorDayTradeMessage

/-- Fractional Prior Day Trade Message: 45 bytes -/
structure FractionalPriorDayTradeMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  saleCondition : Alpha 4
  tradePrice : BitVec 64
  fractionalTradeVolume : BitVec 64
  sellersSaleDays : BitVec 8
  stopStockIndicator : StopStockIndicator
  tradeThroughExemptIndicator : TradeThroughExemptIndicator
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  tradeReportingFacilityId : TradeReportingFacilityId
  priorDayTradeDateAndTime : PriorDayTradeDateAndTime
  deriving DecidableEq, Repr

namespace FractionalPriorDayTradeMessage

def encode (message : FractionalPriorDayTradeMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.saleCondition
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 8 message.fractionalTradeVolume
    ++ (encodeUInt 1 message.sellersSaleDays
    ++ (StopStockIndicator.encode message.stopStockIndicator
    ++ (TradeThroughExemptIndicator.encode message.tradeThroughExemptIndicator
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (PriorDayTradeDateAndTime.encode message.priorDayTradeDateAndTime))))))))))

def decode (bytes : List UInt8) : Option (FractionalPriorDayTradeMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (saleCondition, bytes) ← Alpha.decode 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (fractionalTradeVolume, bytes) ← decodeUInt 8 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (stopStockIndicator, bytes) ← StopStockIndicator.decode bytes
  let (tradeThroughExemptIndicator, bytes) ← TradeThroughExemptIndicator.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (priorDayTradeDateAndTime, bytes) ← PriorDayTradeDateAndTime.decode bytes
  pure ({ securitySymbol, instrumentType, saleCondition, tradePrice, fractionalTradeVolume, sellersSaleDays, stopStockIndicator, tradeThroughExemptIndicator, shortSaleRestrictionIndicator, tradeReportingFacilityId, priorDayTradeDateAndTime }, bytes)

@[simp] theorem encode_length (message : FractionalPriorDayTradeMessage) : (encode message).length = 45 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, StopStockIndicator.encode_length, TradeThroughExemptIndicator.encode_length, ShortSaleRestrictionIndicator.encode_length, TradeReportingFacilityId.encode_length, PriorDayTradeDateAndTime.encode_length]

theorem encode_length_pos (message : FractionalPriorDayTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FractionalPriorDayTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StopStockIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [PriorDayTradeDateAndTime.decode_encode, some_bind]
  rfl

end FractionalPriorDayTradeMessage

/-- Prior Day Trade Cancel Error Message: 42 bytes -/
structure PriorDayTradeCancelErrorMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  saleCondition : Alpha 4
  tradePrice : BitVec 64
  tradeVolume : BitVec 32
  sellersSaleDays : BitVec 8
  stopStockIndicator : StopStockIndicator
  tradeThroughExemptIndicator : TradeThroughExemptIndicator
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  tradeReportingFacilityId : TradeReportingFacilityId
  priorDayTradeDateAndTime : PriorDayTradeDateAndTime
  cancelErrorAction : CancelErrorAction
  deriving DecidableEq, Repr

namespace PriorDayTradeCancelErrorMessage

def encode (message : PriorDayTradeCancelErrorMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.saleCondition
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.tradeVolume
    ++ (encodeUInt 1 message.sellersSaleDays
    ++ (StopStockIndicator.encode message.stopStockIndicator
    ++ (TradeThroughExemptIndicator.encode message.tradeThroughExemptIndicator
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (PriorDayTradeDateAndTime.encode message.priorDayTradeDateAndTime
    ++ (CancelErrorAction.encode message.cancelErrorAction)))))))))))

def decode (bytes : List UInt8) : Option (PriorDayTradeCancelErrorMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (saleCondition, bytes) ← Alpha.decode 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeVolume, bytes) ← decodeUInt 4 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (stopStockIndicator, bytes) ← StopStockIndicator.decode bytes
  let (tradeThroughExemptIndicator, bytes) ← TradeThroughExemptIndicator.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (priorDayTradeDateAndTime, bytes) ← PriorDayTradeDateAndTime.decode bytes
  let (cancelErrorAction, bytes) ← CancelErrorAction.decode bytes
  pure ({ securitySymbol, instrumentType, saleCondition, tradePrice, tradeVolume, sellersSaleDays, stopStockIndicator, tradeThroughExemptIndicator, shortSaleRestrictionIndicator, tradeReportingFacilityId, priorDayTradeDateAndTime, cancelErrorAction }, bytes)

@[simp] theorem encode_length (message : PriorDayTradeCancelErrorMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, StopStockIndicator.encode_length, TradeThroughExemptIndicator.encode_length, ShortSaleRestrictionIndicator.encode_length, TradeReportingFacilityId.encode_length, PriorDayTradeDateAndTime.encode_length, CancelErrorAction.encode_length]

theorem encode_length_pos (message : PriorDayTradeCancelErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriorDayTradeCancelErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StopStockIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriorDayTradeDateAndTime.decode_encode, some_bind]
  dsimp only
  rw [CancelErrorAction.decode_encode, some_bind]
  rfl

end PriorDayTradeCancelErrorMessage

/-- Fractional Prior Day Trade Cancel Error Message: 46 bytes -/
structure FractionalPriorDayTradeCancelErrorMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  saleCondition : Alpha 4
  tradePrice : BitVec 64
  fractionalTradeVolume : BitVec 64
  sellersSaleDays : BitVec 8
  stopStockIndicator : StopStockIndicator
  tradeThroughExemptIndicator : TradeThroughExemptIndicator
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  tradeReportingFacilityId : TradeReportingFacilityId
  priorDayTradeDateAndTime : PriorDayTradeDateAndTime
  cancelErrorAction : CancelErrorAction
  deriving DecidableEq, Repr

namespace FractionalPriorDayTradeCancelErrorMessage

def encode (message : FractionalPriorDayTradeCancelErrorMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.saleCondition
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 8 message.fractionalTradeVolume
    ++ (encodeUInt 1 message.sellersSaleDays
    ++ (StopStockIndicator.encode message.stopStockIndicator
    ++ (TradeThroughExemptIndicator.encode message.tradeThroughExemptIndicator
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (PriorDayTradeDateAndTime.encode message.priorDayTradeDateAndTime
    ++ (CancelErrorAction.encode message.cancelErrorAction)))))))))))

def decode (bytes : List UInt8) : Option (FractionalPriorDayTradeCancelErrorMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (saleCondition, bytes) ← Alpha.decode 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (fractionalTradeVolume, bytes) ← decodeUInt 8 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (stopStockIndicator, bytes) ← StopStockIndicator.decode bytes
  let (tradeThroughExemptIndicator, bytes) ← TradeThroughExemptIndicator.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (priorDayTradeDateAndTime, bytes) ← PriorDayTradeDateAndTime.decode bytes
  let (cancelErrorAction, bytes) ← CancelErrorAction.decode bytes
  pure ({ securitySymbol, instrumentType, saleCondition, tradePrice, fractionalTradeVolume, sellersSaleDays, stopStockIndicator, tradeThroughExemptIndicator, shortSaleRestrictionIndicator, tradeReportingFacilityId, priorDayTradeDateAndTime, cancelErrorAction }, bytes)

@[simp] theorem encode_length (message : FractionalPriorDayTradeCancelErrorMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, StopStockIndicator.encode_length, TradeThroughExemptIndicator.encode_length, ShortSaleRestrictionIndicator.encode_length, TradeReportingFacilityId.encode_length, PriorDayTradeDateAndTime.encode_length, CancelErrorAction.encode_length]

theorem encode_length_pos (message : FractionalPriorDayTradeCancelErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FractionalPriorDayTradeCancelErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StopStockIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriorDayTradeDateAndTime.decode_encode, some_bind]
  dsimp only
  rw [CancelErrorAction.decode_encode, some_bind]
  rfl

end FractionalPriorDayTradeCancelErrorMessage

/-- Any Prior Day Message Payload, selected by Prior Day Message Type -/
inductive PriorDayMessagePayload where
  | priorDayTradeCorrectionMessage (message : PriorDayTradeCorrectionMessage) -- "C" 0x43
  | fractionalPriorDayTradeCorrectionMessage (message : FractionalPriorDayTradeCorrectionMessage) -- "O" 0x4F
  | priorDayTradeMessage (message : PriorDayTradeMessage) -- "T" 0x54
  | fractionalPriorDayTradeMessage (message : FractionalPriorDayTradeMessage) -- "R" 0x52
  | priorDayTradeCancelErrorMessage (message : PriorDayTradeCancelErrorMessage) -- "X" 0x58
  | fractionalPriorDayTradeCancelErrorMessage (message : FractionalPriorDayTradeCancelErrorMessage) -- "E" 0x45
  deriving DecidableEq, Repr

namespace PriorDayMessagePayload

/-- The Prior Day Message Type each message is sent under -/
def tag : PriorDayMessagePayload → BitVec 8
  | .priorDayTradeCorrectionMessage _ => 67
  | .fractionalPriorDayTradeCorrectionMessage _ => 79
  | .priorDayTradeMessage _ => 84
  | .fractionalPriorDayTradeMessage _ => 82
  | .priorDayTradeCancelErrorMessage _ => 88
  | .fractionalPriorDayTradeCancelErrorMessage _ => 69

def encode : PriorDayMessagePayload → List UInt8
  | .priorDayTradeCorrectionMessage message => PriorDayTradeCorrectionMessage.encode message
  | .fractionalPriorDayTradeCorrectionMessage message => FractionalPriorDayTradeCorrectionMessage.encode message
  | .priorDayTradeMessage message => PriorDayTradeMessage.encode message
  | .fractionalPriorDayTradeMessage message => FractionalPriorDayTradeMessage.encode message
  | .priorDayTradeCancelErrorMessage message => PriorDayTradeCancelErrorMessage.encode message
  | .fractionalPriorDayTradeCancelErrorMessage message => FractionalPriorDayTradeCancelErrorMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : PriorDayMessagePayload) : (encode message).length ≤ 77 := by
  cases message with
  | priorDayTradeCorrectionMessage inner =>
    simp only [encode, PriorDayTradeCorrectionMessage.encode_length]
    omega
  | fractionalPriorDayTradeCorrectionMessage inner =>
    simp only [encode, FractionalPriorDayTradeCorrectionMessage.encode_length]
    omega
  | priorDayTradeMessage inner =>
    simp only [encode, PriorDayTradeMessage.encode_length]
    omega
  | fractionalPriorDayTradeMessage inner =>
    simp only [encode, FractionalPriorDayTradeMessage.encode_length]
    omega
  | priorDayTradeCancelErrorMessage inner =>
    simp only [encode, PriorDayTradeCancelErrorMessage.encode_length]
    omega
  | fractionalPriorDayTradeCancelErrorMessage inner =>
    simp only [encode, FractionalPriorDayTradeCancelErrorMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (PriorDayMessagePayload × List UInt8) :=
  if tag = 67 then (PriorDayTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.priorDayTradeCorrectionMessage message, rest)
  else if tag = 79 then (FractionalPriorDayTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.fractionalPriorDayTradeCorrectionMessage message, rest)
  else if tag = 84 then (PriorDayTradeMessage.decode bytes).map fun (message, rest) => (.priorDayTradeMessage message, rest)
  else if tag = 82 then (FractionalPriorDayTradeMessage.decode bytes).map fun (message, rest) => (.fractionalPriorDayTradeMessage message, rest)
  else if tag = 88 then (PriorDayTradeCancelErrorMessage.decode bytes).map fun (message, rest) => (.priorDayTradeCancelErrorMessage message, rest)
  else if tag = 69 then (FractionalPriorDayTradeCancelErrorMessage.decode bytes).map fun (message, rest) => (.fractionalPriorDayTradeCancelErrorMessage message, rest)
  else none

@[simp] theorem decode_encode (message : PriorDayMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end PriorDayMessagePayload

/-- Prior Day Message -/
structure PriorDayMessage where
  priorDayMessagePayload : PriorDayMessagePayload
  deriving DecidableEq, Repr

namespace PriorDayMessage

def encode (message : PriorDayMessage) : List UInt8 :=
  encodeUInt 1 (PriorDayMessagePayload.tag message.priorDayMessagePayload)
    ++ (PriorDayMessagePayload.encode message.priorDayMessagePayload)

def decode (bytes : List UInt8) : Option (PriorDayMessage × List UInt8) := do
  let (priorDayMessageType, bytes) ← decodeUInt 1 bytes
  let (priorDayMessagePayload, bytes) ← PriorDayMessagePayload.decode priorDayMessageType bytes
  pure ({ priorDayMessagePayload }, bytes)

theorem encode_length_pos (message : PriorDayMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PriorDayMessage) : (encode message).length ≤ 78 := by
  unfold encode
  cases message.priorDayMessagePayload with
  | priorDayTradeCorrectionMessage inner =>
    simp only [PriorDayMessagePayload.encode, List.length_append, encodeUInt_length, PriorDayTradeCorrectionMessage.encode_length]
    omega
  | fractionalPriorDayTradeCorrectionMessage inner =>
    simp only [PriorDayMessagePayload.encode, List.length_append, encodeUInt_length, FractionalPriorDayTradeCorrectionMessage.encode_length]
    omega
  | priorDayTradeMessage inner =>
    simp only [PriorDayMessagePayload.encode, List.length_append, encodeUInt_length, PriorDayTradeMessage.encode_length]
    omega
  | fractionalPriorDayTradeMessage inner =>
    simp only [PriorDayMessagePayload.encode, List.length_append, encodeUInt_length, FractionalPriorDayTradeMessage.encode_length]
    omega
  | priorDayTradeCancelErrorMessage inner =>
    simp only [PriorDayMessagePayload.encode, List.length_append, encodeUInt_length, PriorDayTradeCancelErrorMessage.encode_length]
    omega
  | fractionalPriorDayTradeCancelErrorMessage inner =>
    simp only [PriorDayMessagePayload.encode, List.length_append, encodeUInt_length, FractionalPriorDayTradeCancelErrorMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : PriorDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [PriorDayMessagePayload.decode_encode, some_bind]
  rfl

end PriorDayMessage

/-- Auction Status Message: 99 bytes -/
structure AuctionStatusMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  auctionCollarReferencePrice : BitVec 64
  auctionCollarUpperThresholdPrice : BitVec 64
  auctionCollarLowerThresholdPrice : BitVec 64
  numberOfExtensions : BitVec 8
  reserved62 : Alpha 62
  deriving DecidableEq, Repr

namespace AuctionStatusMessage

def encode (message : AuctionStatusMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUInt 8 message.auctionCollarReferencePrice
    ++ (encodeUInt 8 message.auctionCollarUpperThresholdPrice
    ++ (encodeUInt 8 message.auctionCollarLowerThresholdPrice
    ++ (encodeUInt 1 message.numberOfExtensions
    ++ (Alpha.encode message.reserved62))))))

def decode (bytes : List UInt8) : Option (AuctionStatusMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (auctionCollarReferencePrice, bytes) ← decodeUInt 8 bytes
  let (auctionCollarUpperThresholdPrice, bytes) ← decodeUInt 8 bytes
  let (auctionCollarLowerThresholdPrice, bytes) ← decodeUInt 8 bytes
  let (numberOfExtensions, bytes) ← decodeUInt 1 bytes
  let (reserved62, bytes) ← Alpha.decode 62 bytes
  pure ({ securitySymbol, instrumentType, auctionCollarReferencePrice, auctionCollarUpperThresholdPrice, auctionCollarLowerThresholdPrice, numberOfExtensions, reserved62 }, bytes)

@[simp] theorem encode_length (message : AuctionStatusMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AuctionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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

end AuctionStatusMessage

/-- Timestamp 2: 8 bytes -/
structure Timestamp2 where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace Timestamp2

def encode (message : Timestamp2) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (Timestamp2 × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : Timestamp2) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : Timestamp2) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Timestamp2) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Timestamp2

/-- Trade Correction Message: 49 bytes -/
structure TradeCorrectionMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  correctedSaleCondition : Alpha 4
  correctedTradePrice : BitVec 64
  correctedTradeVolume : BitVec 32
  correctedSellersSaleDays : BitVec 8
  correctedStopStockIndicator : Alpha 1
  correctedTradeThroughExemptIndicator : Alpha 1
  correctedShortSaleRestrictionIndicator : Alpha 1
  tradeReportingFacilityId : TradeReportingFacilityId
  timestamp2 : Timestamp2
  originalParticipantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.correctedSaleCondition
    ++ (encodeUInt 8 message.correctedTradePrice
    ++ (encodeUInt 4 message.correctedTradeVolume
    ++ (encodeUInt 1 message.correctedSellersSaleDays
    ++ (Alpha.encode message.correctedStopStockIndicator
    ++ (Alpha.encode message.correctedTradeThroughExemptIndicator
    ++ (Alpha.encode message.correctedShortSaleRestrictionIndicator
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (Timestamp2.encode message.timestamp2
    ++ (encodeUInt 8 message.originalParticipantReferenceNumber)))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (correctedSaleCondition, bytes) ← Alpha.decode 4 bytes
  let (correctedTradePrice, bytes) ← decodeUInt 8 bytes
  let (correctedTradeVolume, bytes) ← decodeUInt 4 bytes
  let (correctedSellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (correctedStopStockIndicator, bytes) ← Alpha.decode 1 bytes
  let (correctedTradeThroughExemptIndicator, bytes) ← Alpha.decode 1 bytes
  let (correctedShortSaleRestrictionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  let (originalParticipantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ securitySymbol, instrumentType, correctedSaleCondition, correctedTradePrice, correctedTradeVolume, correctedSellersSaleDays, correctedStopStockIndicator, correctedTradeThroughExemptIndicator, correctedShortSaleRestrictionIndicator, tradeReportingFacilityId, timestamp2, originalParticipantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, TradeReportingFacilityId.encode_length, Timestamp2.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp2.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCorrectionMessage

/-- Fractional Trade Correction Message: 53 bytes -/
structure FractionalTradeCorrectionMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  correctedSaleCondition : Alpha 4
  correctedTradePrice : BitVec 64
  correctedFractionalTradeVolume : BitVec 64
  correctedSellersSaleDays : BitVec 8
  correctedStopStockIndicator : Alpha 1
  correctedTradeThroughExemptIndicator : Alpha 1
  correctedShortSaleRestrictionIndicator : Alpha 1
  tradeReportingFacilityId : TradeReportingFacilityId
  timestamp2 : Timestamp2
  originalParticipantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace FractionalTradeCorrectionMessage

def encode (message : FractionalTradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.correctedSaleCondition
    ++ (encodeUInt 8 message.correctedTradePrice
    ++ (encodeUInt 8 message.correctedFractionalTradeVolume
    ++ (encodeUInt 1 message.correctedSellersSaleDays
    ++ (Alpha.encode message.correctedStopStockIndicator
    ++ (Alpha.encode message.correctedTradeThroughExemptIndicator
    ++ (Alpha.encode message.correctedShortSaleRestrictionIndicator
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (Timestamp2.encode message.timestamp2
    ++ (encodeUInt 8 message.originalParticipantReferenceNumber)))))))))))

def decode (bytes : List UInt8) : Option (FractionalTradeCorrectionMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (correctedSaleCondition, bytes) ← Alpha.decode 4 bytes
  let (correctedTradePrice, bytes) ← decodeUInt 8 bytes
  let (correctedFractionalTradeVolume, bytes) ← decodeUInt 8 bytes
  let (correctedSellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (correctedStopStockIndicator, bytes) ← Alpha.decode 1 bytes
  let (correctedTradeThroughExemptIndicator, bytes) ← Alpha.decode 1 bytes
  let (correctedShortSaleRestrictionIndicator, bytes) ← Alpha.decode 1 bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  let (originalParticipantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ securitySymbol, instrumentType, correctedSaleCondition, correctedTradePrice, correctedFractionalTradeVolume, correctedSellersSaleDays, correctedStopStockIndicator, correctedTradeThroughExemptIndicator, correctedShortSaleRestrictionIndicator, tradeReportingFacilityId, timestamp2, originalParticipantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : FractionalTradeCorrectionMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, TradeReportingFacilityId.encode_length, Timestamp2.encode_length]

theorem encode_length_pos (message : FractionalTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FractionalTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp2.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FractionalTradeCorrectionMessage

/-- Long Trade Message: 40 bytes -/
structure LongTradeMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  saleCondition : Alpha 4
  tradePrice : BitVec 64
  tradeVolume : BitVec 32
  sellersSaleDays : BitVec 8
  stopStockIndicator : StopStockIndicator
  tradeThroughExemptIndicator : TradeThroughExemptIndicator
  tradeReportingFacilityId : TradeReportingFacilityId
  timestamp2 : Timestamp2
  deriving DecidableEq, Repr

namespace LongTradeMessage

def encode (message : LongTradeMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.saleCondition
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.tradeVolume
    ++ (encodeUInt 1 message.sellersSaleDays
    ++ (StopStockIndicator.encode message.stopStockIndicator
    ++ (TradeThroughExemptIndicator.encode message.tradeThroughExemptIndicator
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (Timestamp2.encode message.timestamp2)))))))))

def decode (bytes : List UInt8) : Option (LongTradeMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (saleCondition, bytes) ← Alpha.decode 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeVolume, bytes) ← decodeUInt 4 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (stopStockIndicator, bytes) ← StopStockIndicator.decode bytes
  let (tradeThroughExemptIndicator, bytes) ← TradeThroughExemptIndicator.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  pure ({ securitySymbol, instrumentType, saleCondition, tradePrice, tradeVolume, sellersSaleDays, stopStockIndicator, tradeThroughExemptIndicator, tradeReportingFacilityId, timestamp2 }, bytes)

@[simp] theorem encode_length (message : LongTradeMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, StopStockIndicator.encode_length, TradeThroughExemptIndicator.encode_length, TradeReportingFacilityId.encode_length, Timestamp2.encode_length]

theorem encode_length_pos (message : LongTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StopStockIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [Timestamp2.decode_encode, some_bind]
  rfl

end LongTradeMessage

/-- Fractional Long Trade Message: 44 bytes -/
structure FractionalLongTradeMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  saleCondition : Alpha 4
  tradePrice : BitVec 64
  fractionalTradeVolume : BitVec 64
  sellersSaleDays : BitVec 8
  stopStockIndicator : StopStockIndicator
  tradeThroughExemptIndicator : TradeThroughExemptIndicator
  tradeReportingFacilityId : TradeReportingFacilityId
  timestamp2 : Timestamp2
  deriving DecidableEq, Repr

namespace FractionalLongTradeMessage

def encode (message : FractionalLongTradeMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.saleCondition
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 8 message.fractionalTradeVolume
    ++ (encodeUInt 1 message.sellersSaleDays
    ++ (StopStockIndicator.encode message.stopStockIndicator
    ++ (TradeThroughExemptIndicator.encode message.tradeThroughExemptIndicator
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (Timestamp2.encode message.timestamp2)))))))))

def decode (bytes : List UInt8) : Option (FractionalLongTradeMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (saleCondition, bytes) ← Alpha.decode 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (fractionalTradeVolume, bytes) ← decodeUInt 8 bytes
  let (sellersSaleDays, bytes) ← decodeUInt 1 bytes
  let (stopStockIndicator, bytes) ← StopStockIndicator.decode bytes
  let (tradeThroughExemptIndicator, bytes) ← TradeThroughExemptIndicator.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  pure ({ securitySymbol, instrumentType, saleCondition, tradePrice, fractionalTradeVolume, sellersSaleDays, stopStockIndicator, tradeThroughExemptIndicator, tradeReportingFacilityId, timestamp2 }, bytes)

@[simp] theorem encode_length (message : FractionalLongTradeMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, StopStockIndicator.encode_length, TradeThroughExemptIndicator.encode_length, TradeReportingFacilityId.encode_length, Timestamp2.encode_length]

theorem encode_length_pos (message : FractionalLongTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FractionalLongTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StopStockIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [Timestamp2.decode_encode, some_bind]
  rfl

end FractionalLongTradeMessage

/-- Trading Status Message: 51 bytes -/
structure TradingStatusMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  lastPriceOpeningReopeningLuldReferencePrice : BitVec 64
  highIndicationPriceUpperLimitPriceBand : BitVec 64
  lowIndicationPriceLowerLimitPriceBand : BitVec 64
  buyVolume : BitVec 32
  sellVolume : BitVec 32
  securityStatus : SecurityStatus
  haltReason : HaltReason
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  tradingStatusId : BitVec 32
  deriving DecidableEq, Repr

namespace TradingStatusMessage

def encode (message : TradingStatusMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUInt 8 message.lastPriceOpeningReopeningLuldReferencePrice
    ++ (encodeUInt 8 message.highIndicationPriceUpperLimitPriceBand
    ++ (encodeUInt 8 message.lowIndicationPriceLowerLimitPriceBand
    ++ (encodeUInt 4 message.buyVolume
    ++ (encodeUInt 4 message.sellVolume
    ++ (SecurityStatus.encode message.securityStatus
    ++ (HaltReason.encode message.haltReason
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (encodeUInt 4 message.tradingStatusId))))))))))

def decode (bytes : List UInt8) : Option (TradingStatusMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (lastPriceOpeningReopeningLuldReferencePrice, bytes) ← decodeUInt 8 bytes
  let (highIndicationPriceUpperLimitPriceBand, bytes) ← decodeUInt 8 bytes
  let (lowIndicationPriceLowerLimitPriceBand, bytes) ← decodeUInt 8 bytes
  let (buyVolume, bytes) ← decodeUInt 4 bytes
  let (sellVolume, bytes) ← decodeUInt 4 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (haltReason, bytes) ← HaltReason.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (tradingStatusId, bytes) ← decodeUInt 4 bytes
  pure ({ securitySymbol, instrumentType, lastPriceOpeningReopeningLuldReferencePrice, highIndicationPriceUpperLimitPriceBand, lowIndicationPriceLowerLimitPriceBand, buyVolume, sellVolume, securityStatus, haltReason, shortSaleRestrictionIndicator, tradingStatusId }, bytes)

@[simp] theorem encode_length (message : TradingStatusMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, SecurityStatus.encode_length, HaltReason.encode_length, ShortSaleRestrictionIndicator.encode_length]

theorem encode_length_pos (message : TradingStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HaltReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradingStatusMessage

/-- Short Trade Message: 31 bytes -/
structure ShortTradeMessage where
  securitySymbol : Alpha 11
  saleCondition : Alpha 4
  saleConditionCategory : SaleConditionCategory
  tradePrice : BitVec 64
  tradeVolume : BitVec 32
  reserved3 : Alpha 3
  deriving DecidableEq, Repr

namespace ShortTradeMessage

def encode (message : ShortTradeMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.saleCondition
    ++ (SaleConditionCategory.encode message.saleConditionCategory
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.tradeVolume
    ++ (Alpha.encode message.reserved3)))))

def decode (bytes : List UInt8) : Option (ShortTradeMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (saleCondition, bytes) ← Alpha.decode 4 bytes
  let (saleConditionCategory, bytes) ← SaleConditionCategory.decode bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeVolume, bytes) ← decodeUInt 4 bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  pure ({ securitySymbol, saleCondition, saleConditionCategory, tradePrice, tradeVolume, reserved3 }, bytes)

@[simp] theorem encode_length (message : ShortTradeMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SaleConditionCategory.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ShortTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ShortTradeMessage

/-- Fractional Short Trade Message: 35 bytes -/
structure FractionalShortTradeMessage where
  securitySymbol : Alpha 11
  saleCondition : Alpha 4
  saleConditionCategory : SaleConditionCategory
  tradePrice : BitVec 64
  fractionalTradeVolume : BitVec 64
  reserved3 : Alpha 3
  deriving DecidableEq, Repr

namespace FractionalShortTradeMessage

def encode (message : FractionalShortTradeMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.saleCondition
    ++ (SaleConditionCategory.encode message.saleConditionCategory
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 8 message.fractionalTradeVolume
    ++ (Alpha.encode message.reserved3)))))

def decode (bytes : List UInt8) : Option (FractionalShortTradeMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (saleCondition, bytes) ← Alpha.decode 4 bytes
  let (saleConditionCategory, bytes) ← SaleConditionCategory.decode bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (fractionalTradeVolume, bytes) ← decodeUInt 8 bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  pure ({ securitySymbol, saleCondition, saleConditionCategory, tradePrice, fractionalTradeVolume, reserved3 }, bytes)

@[simp] theorem encode_length (message : FractionalShortTradeMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SaleConditionCategory.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FractionalShortTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FractionalShortTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleConditionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FractionalShortTradeMessage

/-- Trade Cancel Error Message: 31 bytes -/
structure TradeCancelErrorMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  tradeThroughExemptIndicator : TradeThroughExemptIndicator
  tradeReportingFacilityId : TradeReportingFacilityId
  originalParticipantReferenceNumber : BitVec 64
  timestamp2 : Timestamp2
  cancelErrorAction : CancelErrorAction
  deriving DecidableEq, Repr

namespace TradeCancelErrorMessage

def encode (message : TradeCancelErrorMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (TradeThroughExemptIndicator.encode message.tradeThroughExemptIndicator
    ++ (TradeReportingFacilityId.encode message.tradeReportingFacilityId
    ++ (encodeUInt 8 message.originalParticipantReferenceNumber
    ++ (Timestamp2.encode message.timestamp2
    ++ (CancelErrorAction.encode message.cancelErrorAction))))))

def decode (bytes : List UInt8) : Option (TradeCancelErrorMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (tradeThroughExemptIndicator, bytes) ← TradeThroughExemptIndicator.decode bytes
  let (tradeReportingFacilityId, bytes) ← TradeReportingFacilityId.decode bytes
  let (originalParticipantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  let (cancelErrorAction, bytes) ← CancelErrorAction.decode bytes
  pure ({ securitySymbol, instrumentType, tradeThroughExemptIndicator, tradeReportingFacilityId, originalParticipantReferenceNumber, timestamp2, cancelErrorAction }, bytes)

@[simp] theorem encode_length (message : TradeCancelErrorMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, TradeThroughExemptIndicator.encode_length, TradeReportingFacilityId.encode_length, encodeUInt_length, Timestamp2.encode_length, CancelErrorAction.encode_length]

theorem encode_length_pos (message : TradeCancelErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeThroughExemptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeReportingFacilityId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp2.decode_encode, some_bind]
  dsimp only
  rw [CancelErrorAction.decode_encode, some_bind]
  rfl

end TradeCancelErrorMessage

/-- Any Trade Message Payload, selected by Trade Message Type -/
inductive TradeMessagePayload where
  | auctionStatusMessage (message : AuctionStatusMessage) -- "A" 0x41
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "C" 0x43
  | fractionalTradeCorrectionMessage (message : FractionalTradeCorrectionMessage) -- "O" 0x4F
  | longTradeMessage (message : LongTradeMessage) -- "L" 0x4C
  | fractionalLongTradeMessage (message : FractionalLongTradeMessage) -- "R" 0x52
  | tradingStatusMessage (message : TradingStatusMessage) -- "S" 0x53
  | shortTradeMessage (message : ShortTradeMessage) -- "T" 0x54
  | fractionalShortTradeMessage (message : FractionalShortTradeMessage) -- "H" 0x48
  | tradeCancelErrorMessage (message : TradeCancelErrorMessage) -- "X" 0x58
  deriving DecidableEq, Repr

namespace TradeMessagePayload

/-- The Trade Message Type each message is sent under -/
def tag : TradeMessagePayload → BitVec 8
  | .auctionStatusMessage _ => 65
  | .tradeCorrectionMessage _ => 67
  | .fractionalTradeCorrectionMessage _ => 79
  | .longTradeMessage _ => 76
  | .fractionalLongTradeMessage _ => 82
  | .tradingStatusMessage _ => 83
  | .shortTradeMessage _ => 84
  | .fractionalShortTradeMessage _ => 72
  | .tradeCancelErrorMessage _ => 88

def encode : TradeMessagePayload → List UInt8
  | .auctionStatusMessage message => AuctionStatusMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message
  | .fractionalTradeCorrectionMessage message => FractionalTradeCorrectionMessage.encode message
  | .longTradeMessage message => LongTradeMessage.encode message
  | .fractionalLongTradeMessage message => FractionalLongTradeMessage.encode message
  | .tradingStatusMessage message => TradingStatusMessage.encode message
  | .shortTradeMessage message => ShortTradeMessage.encode message
  | .fractionalShortTradeMessage message => FractionalShortTradeMessage.encode message
  | .tradeCancelErrorMessage message => TradeCancelErrorMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : TradeMessagePayload) : (encode message).length ≤ 99 := by
  cases message with
  | auctionStatusMessage inner =>
    simp only [encode, AuctionStatusMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega
  | fractionalTradeCorrectionMessage inner =>
    simp only [encode, FractionalTradeCorrectionMessage.encode_length]
    omega
  | longTradeMessage inner =>
    simp only [encode, LongTradeMessage.encode_length]
    omega
  | fractionalLongTradeMessage inner =>
    simp only [encode, FractionalLongTradeMessage.encode_length]
    omega
  | tradingStatusMessage inner =>
    simp only [encode, TradingStatusMessage.encode_length]
    omega
  | shortTradeMessage inner =>
    simp only [encode, ShortTradeMessage.encode_length]
    omega
  | fractionalShortTradeMessage inner =>
    simp only [encode, FractionalShortTradeMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [encode, TradeCancelErrorMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (TradeMessagePayload × List UInt8) :=
  if tag = 65 then (AuctionStatusMessage.decode bytes).map fun (message, rest) => (.auctionStatusMessage message, rest)
  else if tag = 67 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else if tag = 79 then (FractionalTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.fractionalTradeCorrectionMessage message, rest)
  else if tag = 76 then (LongTradeMessage.decode bytes).map fun (message, rest) => (.longTradeMessage message, rest)
  else if tag = 82 then (FractionalLongTradeMessage.decode bytes).map fun (message, rest) => (.fractionalLongTradeMessage message, rest)
  else if tag = 83 then (TradingStatusMessage.decode bytes).map fun (message, rest) => (.tradingStatusMessage message, rest)
  else if tag = 84 then (ShortTradeMessage.decode bytes).map fun (message, rest) => (.shortTradeMessage message, rest)
  else if tag = 72 then (FractionalShortTradeMessage.decode bytes).map fun (message, rest) => (.fractionalShortTradeMessage message, rest)
  else if tag = 88 then (TradeCancelErrorMessage.decode bytes).map fun (message, rest) => (.tradeCancelErrorMessage message, rest)
  else none

@[simp] theorem decode_encode (message : TradeMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end TradeMessagePayload

/-- Trade Message -/
structure TradeMessage where
  tradeMessagePayload : TradeMessagePayload
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 1 (TradeMessagePayload.tag message.tradeMessagePayload)
    ++ (TradeMessagePayload.encode message.tradeMessagePayload)

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (tradeMessageType, bytes) ← decodeUInt 1 bytes
  let (tradeMessagePayload, bytes) ← TradeMessagePayload.decode tradeMessageType bytes
  pure ({ tradeMessagePayload }, bytes)

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeMessage) : (encode message).length ≤ 100 := by
  unfold encode
  cases message.tradeMessagePayload with
  | auctionStatusMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, AuctionStatusMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, TradeCorrectionMessage.encode_length]
    omega
  | fractionalTradeCorrectionMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, FractionalTradeCorrectionMessage.encode_length]
    omega
  | longTradeMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, LongTradeMessage.encode_length]
    omega
  | fractionalLongTradeMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, FractionalLongTradeMessage.encode_length]
    omega
  | tradingStatusMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, TradingStatusMessage.encode_length]
    omega
  | shortTradeMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, ShortTradeMessage.encode_length]
    omega
  | fractionalShortTradeMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, FractionalShortTradeMessage.encode_length]
    omega
  | tradeCancelErrorMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, TradeCancelErrorMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TradeMessagePayload.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Any Category Payload, selected by Message Category -/
inductive CategoryPayload where
  | administrativeMessage (message : AdministrativeMessage) -- "A" 0x41
  | controlMessage (message : ControlMessage) -- "C" 0x43
  | indicesMessage (message : IndicesMessage) -- "I" 0x49
  | marketStatusMessage (message : MarketStatusMessage) -- "M" 0x4D
  | priorDayMessage (message : PriorDayMessage) -- "P" 0x50
  | tradeMessage (message : TradeMessage) -- "T" 0x54
  deriving DecidableEq, Repr

namespace CategoryPayload

/-- The Message Category each message is sent under -/
def tag : CategoryPayload → BitVec 8
  | .administrativeMessage _ => 65
  | .controlMessage _ => 67
  | .indicesMessage _ => 73
  | .marketStatusMessage _ => 77
  | .priorDayMessage _ => 80
  | .tradeMessage _ => 84

def encode : CategoryPayload → List UInt8
  | .administrativeMessage message => AdministrativeMessage.encode message
  | .controlMessage message => ControlMessage.encode message
  | .indicesMessage message => IndicesMessage.encode message
  | .marketStatusMessage message => MarketStatusMessage.encode message
  | .priorDayMessage message => PriorDayMessage.encode message
  | .tradeMessage message => TradeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : CategoryPayload) : (encode message).length ≤ 257 := by
  cases message with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega
  | controlMessage inner =>
    have bound_inner := ControlMessage.encode_length_le inner
    simp only [encode]
    omega
  | indicesMessage inner =>
    have bound_inner := IndicesMessage.encode_length_le inner
    simp only [encode]
    omega
  | marketStatusMessage inner =>
    have bound_inner := MarketStatusMessage.encode_length_le inner
    simp only [encode]
    omega
  | priorDayMessage inner =>
    have bound_inner := PriorDayMessage.encode_length_le inner
    simp only [encode]
    omega
  | tradeMessage inner =>
    have bound_inner := TradeMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (CategoryPayload × List UInt8) :=
  if tag = 65 then (AdministrativeMessage.decode bytes).map fun (message, rest) => (.administrativeMessage message, rest)
  else if tag = 67 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage message, rest)
  else if tag = 73 then (IndicesMessage.decode bytes).map fun (message, rest) => (.indicesMessage message, rest)
  else if tag = 77 then (MarketStatusMessage.decode bytes).map fun (message, rest) => (.marketStatusMessage message, rest)
  else if tag = 80 then (PriorDayMessage.decode bytes).map fun (message, rest) => (.priorDayMessage message, rest)
  else if tag = 84 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else none

@[simp] theorem decode_encode (message : CategoryPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end CategoryPayload

/-- Message -/
structure Message where
  messageLength : BitVec 16
  messageType : Alpha 1
  participantId : Alpha 1
  timestamp1 : Timestamp1
  messageId : BitVec 8
  reserved : Alpha 4
  participantReferenceNumber : BitVec 64
  categoryPayload : CategoryPayload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUInt 2 message.messageLength
    ++ (encodeUInt 1 (CategoryPayload.tag message.categoryPayload)
    ++ (Alpha.encode message.messageType
    ++ (Alpha.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (Alpha.encode message.reserved
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (CategoryPayload.encode message.categoryPayload))))))))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (messageCategory, bytes) ← decodeUInt 1 bytes
  let (messageType, bytes) ← Alpha.decode 1 bytes
  let (participantId, bytes) ← Alpha.decode 1 bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (reserved, bytes) ← Alpha.decode 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (categoryPayload, bytes) ← CategoryPayload.decode messageCategory bytes
  pure ({ messageLength, messageType, participantId, timestamp1, messageId, reserved, participantReferenceNumber, categoryPayload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 283 := by
  unfold encode
  cases message.categoryPayload with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Timestamp1.encode_length]
    omega
  | controlMessage inner =>
    have bound_inner := ControlMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Timestamp1.encode_length]
    omega
  | indicesMessage inner =>
    have bound_inner := IndicesMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Timestamp1.encode_length]
    omega
  | marketStatusMessage inner =>
    have bound_inner := MarketStatusMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Timestamp1.encode_length]
    omega
  | priorDayMessage inner =>
    have bound_inner := PriorDayMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Timestamp1.encode_length]
    omega
  | tradeMessage inner =>
    have bound_inner := TradeMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Timestamp1.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CategoryPayload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  blockSeparator : BitVec 16
  version : BitVec 8
  blockSize : BitVec 16
  blockSequenceNumber : BitVec 32
  blockChecksum : BitVec 16
  message : Bounded 1 Message
  blockPadByte : Capped 1
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 message.blockSeparator
    ++ (encodeUInt 1 message.version
    ++ (encodeUInt 2 message.blockSize
    ++ (encodeUInt 4 message.blockSequenceNumber
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUInt 2 message.blockChecksum
    ++ (encodeMany Message.encode message.message.val
    ++ (message.blockPadByte.val)))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (blockSeparator, bytes) ← decodeUInt 2 bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (blockSize, bytes) ← decodeUInt 2 bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (messagesInBlock, bytes) ← decodeUInt 1 bytes
  let (blockChecksum, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messagesInBlock.toNat bytes
  let blockPadByte_ := bytes
  if fits_message : message_.length < 256 ^ 1 then
    if fits_blockPadByte : blockPadByte_.length ≤ 1 then
      pure { blockSeparator, version, blockSize, blockSequenceNumber, blockChecksum, message := ⟨message_, fits_message⟩, blockPadByte := ⟨blockPadByte_, fits_blockPadByte⟩ }
    else none
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 72178 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 283 Message.encode_length_le message.message.val
  have bound_blockPadByte := message.blockPadByte.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt, dite_eq_left message.blockPadByte.length_le]
  rfl

end Packet

end Omi.SiacCtsInputCtaV27F
