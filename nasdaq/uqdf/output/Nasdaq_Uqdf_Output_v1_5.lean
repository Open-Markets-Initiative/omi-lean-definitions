import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Output v1.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Nbbo Appendage Indicator chooses the Short Form National Bbo Appendage or Long Form National Bbo Appendage attached, or none: it is written from the choice, and a value it does not list is not decoded.

Note: Finra Adf Mpid Appendage Indicator chooses the Finra Adf Mpid Appendage attached, or none: it is written from the choice, and a value it does not list is not decoded.

Note: Message's Message Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqUqdfOutputUtpV15

/-- Market Center Originator Id: one byte code -/
def MarketCenterOriginatorId.codes : List UInt8 :=
  [0x59, 0x5A, 0x4A, 0x4B, 0x57, 0x42, 0x58, 0x51, 0x49, 0x4E, 0x50, 0x41, 0x43, 0x4D, 0x44, 0x56, 0x4C, 0x48, 0x55, 0x45]

inductive MarketCenterOriginatorId where
  | byx -- Byx
  | bzx -- Bzx
  | edga -- Edga
  | edgx -- Edgx
  | cboe -- Cboe
  | bx -- Bx
  | phlx -- Phlx
  | nasdaq -- Nasdaq
  | ise -- Ise
  | nyse -- Nyse
  | arca -- Arca
  | american -- American
  | national -- National
  | chicago -- Chicago
  | finra -- Finra
  | iex -- Iex
  | ltse -- Ltse
  | pearl -- Pearl
  | memx -- Memx
  | marketIndependent -- Market Independent
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCenterOriginatorId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCenterOriginatorId

def toByte : MarketCenterOriginatorId → UInt8
  | .byx => 0x59
  | .bzx => 0x5A
  | .edga => 0x4A
  | .edgx => 0x4B
  | .cboe => 0x57
  | .bx => 0x42
  | .phlx => 0x58
  | .nasdaq => 0x51
  | .ise => 0x49
  | .nyse => 0x4E
  | .arca => 0x50
  | .american => 0x41
  | .national => 0x43
  | .chicago => 0x4D
  | .finra => 0x44
  | .iex => 0x56
  | .ltse => 0x4C
  | .pearl => 0x48
  | .memx => 0x55
  | .marketIndependent => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCenterOriginatorId :=
  if byte = 0x59 then .byx
  else if byte = 0x5A then .bzx
  else if byte = 0x4A then .edga
  else if byte = 0x4B then .edgx
  else if byte = 0x57 then .cboe
  else if byte = 0x42 then .bx
  else if byte = 0x58 then .phlx
  else if byte = 0x51 then .nasdaq
  else if byte = 0x49 then .ise
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .arca
  else if byte = 0x41 then .american
  else if byte = 0x43 then .national
  else if byte = 0x4D then .chicago
  else if byte = 0x44 then .finra
  else if byte = 0x56 then .iex
  else if byte = 0x4C then .ltse
  else if byte = 0x48 then .pearl
  else if byte = 0x55 then .memx
  else .marketIndependent

def ofByte (byte : UInt8) : MarketCenterOriginatorId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCenterOriginatorId) : ofByte value.toByte = value := by
  cases value with
  | byx => decide
  | bzx => decide
  | edga => decide
  | edgx => decide
  | cboe => decide
  | bx => decide
  | phlx => decide
  | nasdaq => decide
  | ise => decide
  | nyse => decide
  | arca => decide
  | american => decide
  | national => decide
  | chicago => decide
  | finra => decide
  | iex => decide
  | ltse => decide
  | pearl => decide
  | memx => decide
  | marketIndependent => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCenterOriginatorId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCenterOriginatorId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCenterOriginatorId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCenterOriginatorId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCenterOriginatorId

/-- Sub Market Center Id: one byte code -/
def SubMarketCenterId.codes : List UInt8 :=
  [0x4E, 0x51, 0x42, 0x20]

inductive SubMarketCenterId where
  | nyseTrf -- Nyse Trf
  | nasdaqTrfCarteret -- Nasdaq Trf Carteret
  | nasdaqTrfChicago -- Nasdaq Trf Chicago
  | finraAlternativeDisplayFacility -- Finra Alternative Display Facility
  | unlisted (byte : { byte : UInt8 // byte ∉ SubMarketCenterId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SubMarketCenterId

def toByte : SubMarketCenterId → UInt8
  | .nyseTrf => 0x4E
  | .nasdaqTrfCarteret => 0x51
  | .nasdaqTrfChicago => 0x42
  | .finraAlternativeDisplayFacility => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SubMarketCenterId :=
  if byte = 0x4E then .nyseTrf
  else if byte = 0x51 then .nasdaqTrfCarteret
  else if byte = 0x42 then .nasdaqTrfChicago
  else .finraAlternativeDisplayFacility

def ofByte (byte : UInt8) : SubMarketCenterId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SubMarketCenterId) : ofByte value.toByte = value := by
  cases value with
  | nyseTrf => decide
  | nasdaqTrfCarteret => decide
  | nasdaqTrfChicago => decide
  | finraAlternativeDisplayFacility => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SubMarketCenterId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SubMarketCenterId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SubMarketCenterId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SubMarketCenterId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SubMarketCenterId

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x46, 0x48, 0x49, 0x4C, 0x4E, 0x4F, 0x52, 0x55, 0x58, 0x59, 0x5A, 0x34]

inductive QuoteCondition where
  | manualAskAutomatedBid -- Manual Ask Automated Bid
  | manualBidAutomatedAsk -- Manual Bid Automated Ask
  | fastTrading -- Fast Trading
  | manualBidAndAsk -- Manual Bid And Ask
  | orderImbalance -- Order Imbalance
  | closedQuote -- Closed Quote
  | nonFirmQuote -- Non Firm Quote
  | openingQuoteAutomated -- Opening Quote Automated
  | regularTwoSidedOpenQuoteAutomated -- Regular Two Sided Open Quote Automated
  | manualBidAndAskNonFirm -- Manual Bid And Ask Non Firm
  | orderInflux -- Order Influx
  | automatedBidNoOfferOrAutomatedOfferNoBid -- Automated Bid No Offer Or Automated Offer No Bid
  | noOpenNoResume -- No Open No Resume
  | intradayAuction -- Intraday Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .manualAskAutomatedBid => 0x41
  | .manualBidAutomatedAsk => 0x42
  | .fastTrading => 0x46
  | .manualBidAndAsk => 0x48
  | .orderImbalance => 0x49
  | .closedQuote => 0x4C
  | .nonFirmQuote => 0x4E
  | .openingQuoteAutomated => 0x4F
  | .regularTwoSidedOpenQuoteAutomated => 0x52
  | .manualBidAndAskNonFirm => 0x55
  | .orderInflux => 0x58
  | .automatedBidNoOfferOrAutomatedOfferNoBid => 0x59
  | .noOpenNoResume => 0x5A
  | .intradayAuction => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x41 then .manualAskAutomatedBid
  else if byte = 0x42 then .manualBidAutomatedAsk
  else if byte = 0x46 then .fastTrading
  else if byte = 0x48 then .manualBidAndAsk
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x4C then .closedQuote
  else if byte = 0x4E then .nonFirmQuote
  else if byte = 0x4F then .openingQuoteAutomated
  else if byte = 0x52 then .regularTwoSidedOpenQuoteAutomated
  else if byte = 0x55 then .manualBidAndAskNonFirm
  else if byte = 0x58 then .orderInflux
  else if byte = 0x59 then .automatedBidNoOfferOrAutomatedOfferNoBid
  else if byte = 0x5A then .noOpenNoResume
  else .intradayAuction

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | manualAskAutomatedBid => decide
  | manualBidAutomatedAsk => decide
  | fastTrading => decide
  | manualBidAndAsk => decide
  | orderImbalance => decide
  | closedQuote => decide
  | nonFirmQuote => decide
  | openingQuoteAutomated => decide
  | regularTwoSidedOpenQuoteAutomated => decide
  | manualBidAndAskNonFirm => decide
  | orderInflux => decide
  | automatedBidNoOfferOrAutomatedOfferNoBid => decide
  | noOpenNoResume => decide
  | intradayAuction => decide
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

/-- Sip Generated Update: one byte code -/
def SipGeneratedUpdate.codes : List UInt8 :=
  [0x20, 0x45]

inductive SipGeneratedUpdate where
  | originatedFromTheMarketParticipant -- Originated From The Market Participant
  | siPgeneratedTransaction -- Si Pgenerated Transaction
  | unlisted (byte : { byte : UInt8 // byte ∉ SipGeneratedUpdate.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SipGeneratedUpdate

def toByte : SipGeneratedUpdate → UInt8
  | .originatedFromTheMarketParticipant => 0x20
  | .siPgeneratedTransaction => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SipGeneratedUpdate :=
  if byte = 0x20 then .originatedFromTheMarketParticipant
  else .siPgeneratedTransaction

def ofByte (byte : UInt8) : SipGeneratedUpdate :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SipGeneratedUpdate) : ofByte value.toByte = value := by
  cases value with
  | originatedFromTheMarketParticipant => decide
  | siPgeneratedTransaction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SipGeneratedUpdate) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SipGeneratedUpdate × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SipGeneratedUpdate) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SipGeneratedUpdate) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SipGeneratedUpdate

/-- Luld Bbo Indicator: one byte code -/
def LuldBboIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43]

inductive LuldBboIndicator where
  | notApplicable -- Not Applicable
  | bidPriceAboveUpperLimitPriceBand -- Bid Price Above Upper Limit Price Band
  | askPriceBelowLowerLimitPriceBand -- Ask Price Below Lower Limit Price Band
  | bidAndAskOutsidePriceBand -- Bid And Ask Outside Price Band
  | unlisted (byte : { byte : UInt8 // byte ∉ LuldBboIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LuldBboIndicator

def toByte : LuldBboIndicator → UInt8
  | .notApplicable => 0x20
  | .bidPriceAboveUpperLimitPriceBand => 0x41
  | .askPriceBelowLowerLimitPriceBand => 0x42
  | .bidAndAskOutsidePriceBand => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LuldBboIndicator :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x41 then .bidPriceAboveUpperLimitPriceBand
  else if byte = 0x42 then .askPriceBelowLowerLimitPriceBand
  else .bidAndAskOutsidePriceBand

def ofByte (byte : UInt8) : LuldBboIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LuldBboIndicator) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | bidPriceAboveUpperLimitPriceBand => decide
  | askPriceBelowLowerLimitPriceBand => decide
  | bidAndAskOutsidePriceBand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LuldBboIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LuldBboIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LuldBboIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LuldBboIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LuldBboIndicator

/-- Retail Interest Indicator: one byte code -/
def RetailInterestIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43]

inductive RetailInterestIndicator where
  | notApplicable -- Not Applicable
  | onBidQuote -- On Bid Quote
  | onAskQuote -- On Ask Quote
  | onBothBidAndAskQuote -- On Both Bid And Ask Quote
  | unlisted (byte : { byte : UInt8 // byte ∉ RetailInterestIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetailInterestIndicator

def toByte : RetailInterestIndicator → UInt8
  | .notApplicable => 0x20
  | .onBidQuote => 0x41
  | .onAskQuote => 0x42
  | .onBothBidAndAskQuote => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RetailInterestIndicator :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x41 then .onBidQuote
  else if byte = 0x42 then .onAskQuote
  else .onBothBidAndAskQuote

def ofByte (byte : UInt8) : RetailInterestIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetailInterestIndicator) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | onBidQuote => decide
  | onAskQuote => decide
  | onBothBidAndAskQuote => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RetailInterestIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetailInterestIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RetailInterestIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RetailInterestIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RetailInterestIndicator

/-- Luld National Bbo Indicator: one byte code -/
def LuldNationalBboIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49]

inductive LuldNationalBboIndicator where
  | notApplicable -- Not Applicable
  | nationalBestBidAndNationalBestAskAreExecutable -- National Best Bid And National Best Ask Are Executable
  | nationalBestBidBelowLowerLimitPriceBand -- National Best Bid Below Lower Limit Price Band
  | nationalBestAskAboveUpperLimitPriceBand -- National Best Ask Above Upper Limit Price Band
  | nationalBestBidBelowLowerLimitPriceBandAndNationalBestAskAboveUpperLimitPriceBand -- National Best Bid Below Lower Limit Price Band And National Best Ask Above Upper Limit Price Band
  | nationalBestBidEqualsUpperLimitPriceBand -- National Best Bid Equals Upper Limit Price Band
  | nationalBestOfferEqualsLowerLimitPriceBand -- National Best Offer Equals Lower Limit Price Band
  | nationalBestBidEqualsUpperLimitPriceBand_47 -- National Best Bid Equals Upper Limit Price Band
  | nationalBestAskEqualsLowerLimitPriceBand -- National Best Ask Equals Lower Limit Price Band
  | nationalBestBidEqualsUpperLimitPriceBandAndNationalBestAskEqualsLowerLimitPriceBand -- National Best Bid Equals Upper Limit Price Band And National Best Ask Equals Lower Limit Price Band
  | unlisted (byte : { byte : UInt8 // byte ∉ LuldNationalBboIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LuldNationalBboIndicator

def toByte : LuldNationalBboIndicator → UInt8
  | .notApplicable => 0x20
  | .nationalBestBidAndNationalBestAskAreExecutable => 0x41
  | .nationalBestBidBelowLowerLimitPriceBand => 0x42
  | .nationalBestAskAboveUpperLimitPriceBand => 0x43
  | .nationalBestBidBelowLowerLimitPriceBandAndNationalBestAskAboveUpperLimitPriceBand => 0x44
  | .nationalBestBidEqualsUpperLimitPriceBand => 0x45
  | .nationalBestOfferEqualsLowerLimitPriceBand => 0x46
  | .nationalBestBidEqualsUpperLimitPriceBand_47 => 0x47
  | .nationalBestAskEqualsLowerLimitPriceBand => 0x48
  | .nationalBestBidEqualsUpperLimitPriceBandAndNationalBestAskEqualsLowerLimitPriceBand => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LuldNationalBboIndicator :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x41 then .nationalBestBidAndNationalBestAskAreExecutable
  else if byte = 0x42 then .nationalBestBidBelowLowerLimitPriceBand
  else if byte = 0x43 then .nationalBestAskAboveUpperLimitPriceBand
  else if byte = 0x44 then .nationalBestBidBelowLowerLimitPriceBandAndNationalBestAskAboveUpperLimitPriceBand
  else if byte = 0x45 then .nationalBestBidEqualsUpperLimitPriceBand
  else if byte = 0x46 then .nationalBestOfferEqualsLowerLimitPriceBand
  else if byte = 0x47 then .nationalBestBidEqualsUpperLimitPriceBand_47
  else if byte = 0x48 then .nationalBestAskEqualsLowerLimitPriceBand
  else .nationalBestBidEqualsUpperLimitPriceBandAndNationalBestAskEqualsLowerLimitPriceBand

def ofByte (byte : UInt8) : LuldNationalBboIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LuldNationalBboIndicator) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | nationalBestBidAndNationalBestAskAreExecutable => decide
  | nationalBestBidBelowLowerLimitPriceBand => decide
  | nationalBestAskAboveUpperLimitPriceBand => decide
  | nationalBestBidBelowLowerLimitPriceBandAndNationalBestAskAboveUpperLimitPriceBand => decide
  | nationalBestBidEqualsUpperLimitPriceBand => decide
  | nationalBestOfferEqualsLowerLimitPriceBand => decide
  | nationalBestBidEqualsUpperLimitPriceBand_47 => decide
  | nationalBestAskEqualsLowerLimitPriceBand => decide
  | nationalBestBidEqualsUpperLimitPriceBandAndNationalBestAskEqualsLowerLimitPriceBand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LuldNationalBboIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LuldNationalBboIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LuldNationalBboIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LuldNationalBboIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LuldNationalBboIndicator

/-- Nbbo Quote Condition: one byte code -/
def NbboQuoteCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x46, 0x48, 0x49, 0x4C, 0x4E, 0x4F, 0x52, 0x55, 0x58, 0x59, 0x5A, 0x34]

inductive NbboQuoteCondition where
  | manualAskAutomatedBid -- Manual Ask Automated Bid
  | manualBidAutomatedAsk -- Manual Bid Automated Ask
  | fastTrading -- Fast Trading
  | manualBidAndAsk -- Manual Bid And Ask
  | orderImbalance -- Order Imbalance
  | closedQuote -- Closed Quote
  | nonFirmQuote -- Non Firm Quote
  | openingQuoteAutomated -- Opening Quote Automated
  | regularTwoSidedOpenQuoteAutomated -- Regular Two Sided Open Quote Automated
  | manualBidAndAskNonFirm -- Manual Bid And Ask Non Firm
  | orderInflux -- Order Influx
  | automatedBidNoOfferOrAutomatedOfferNoBid -- Automated Bid No Offer Or Automated Offer No Bid
  | noOpenNoResume -- No Open No Resume
  | intradayAuction -- Intraday Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ NbboQuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NbboQuoteCondition

def toByte : NbboQuoteCondition → UInt8
  | .manualAskAutomatedBid => 0x41
  | .manualBidAutomatedAsk => 0x42
  | .fastTrading => 0x46
  | .manualBidAndAsk => 0x48
  | .orderImbalance => 0x49
  | .closedQuote => 0x4C
  | .nonFirmQuote => 0x4E
  | .openingQuoteAutomated => 0x4F
  | .regularTwoSidedOpenQuoteAutomated => 0x52
  | .manualBidAndAskNonFirm => 0x55
  | .orderInflux => 0x58
  | .automatedBidNoOfferOrAutomatedOfferNoBid => 0x59
  | .noOpenNoResume => 0x5A
  | .intradayAuction => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NbboQuoteCondition :=
  if byte = 0x41 then .manualAskAutomatedBid
  else if byte = 0x42 then .manualBidAutomatedAsk
  else if byte = 0x46 then .fastTrading
  else if byte = 0x48 then .manualBidAndAsk
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x4C then .closedQuote
  else if byte = 0x4E then .nonFirmQuote
  else if byte = 0x4F then .openingQuoteAutomated
  else if byte = 0x52 then .regularTwoSidedOpenQuoteAutomated
  else if byte = 0x55 then .manualBidAndAskNonFirm
  else if byte = 0x58 then .orderInflux
  else if byte = 0x59 then .automatedBidNoOfferOrAutomatedOfferNoBid
  else if byte = 0x5A then .noOpenNoResume
  else .intradayAuction

def ofByte (byte : UInt8) : NbboQuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NbboQuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | manualAskAutomatedBid => decide
  | manualBidAutomatedAsk => decide
  | fastTrading => decide
  | manualBidAndAsk => decide
  | orderImbalance => decide
  | closedQuote => decide
  | nonFirmQuote => decide
  | openingQuoteAutomated => decide
  | regularTwoSidedOpenQuoteAutomated => decide
  | manualBidAndAskNonFirm => decide
  | orderInflux => decide
  | automatedBidNoOfferOrAutomatedOfferNoBid => decide
  | noOpenNoResume => decide
  | intradayAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NbboQuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NbboQuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NbboQuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NbboQuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NbboQuoteCondition

/-- Trading Action Code: one byte code -/
def TradingActionCode.codes : List UInt8 :=
  [0x48, 0x51, 0x54, 0x50]

inductive TradingActionCode where
  | tradingHalt -- Trading Halt
  | quotationResumptionIncludingAfterEma -- Quotation Resumption Including After Ema
  | tradingResumption -- Trading Resumption
  | volatilityTradingPause -- Volatility Trading Pause
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingActionCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingActionCode

def toByte : TradingActionCode → UInt8
  | .tradingHalt => 0x48
  | .quotationResumptionIncludingAfterEma => 0x51
  | .tradingResumption => 0x54
  | .volatilityTradingPause => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingActionCode :=
  if byte = 0x48 then .tradingHalt
  else if byte = 0x51 then .quotationResumptionIncludingAfterEma
  else if byte = 0x54 then .tradingResumption
  else .volatilityTradingPause

def ofByte (byte : UInt8) : TradingActionCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingActionCode) : ofByte value.toByte = value := by
  cases value with
  | tradingHalt => decide
  | quotationResumptionIncludingAfterEma => decide
  | tradingResumption => decide
  | volatilityTradingPause => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingActionCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingActionCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingActionCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingActionCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingActionCode

/-- Issue Type: one byte code -/
def IssueType.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x46, 0x49, 0x4C, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57]

inductive IssueType where
  | americanDepositoryReceipt -- American Depository Receipt
  | bond -- Bond
  | commonStock -- Common Stock
  | depositoryReceipt -- Depository Receipt
  | rule144a -- Rule 144a
  | limitedPartnership -- Limited Partnership
  | note -- Note
  | ordinaryShares -- Ordinary Shares
  | preferredStock -- Preferred Stock
  | otherSecurities -- Other Securities
  | rights -- Rights
  | sharesOfBeneficialInterest -- Shares Of Beneficial Interest
  | convertibleDebenture -- Convertible Debenture
  | unit -- Unit
  | unitsOfBeneficialInterest -- Units Of Beneficial Interest
  | warrant -- Warrant
  | unlisted (byte : { byte : UInt8 // byte ∉ IssueType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IssueType

def toByte : IssueType → UInt8
  | .americanDepositoryReceipt => 0x41
  | .bond => 0x42
  | .commonStock => 0x43
  | .depositoryReceipt => 0x46
  | .rule144a => 0x49
  | .limitedPartnership => 0x4C
  | .note => 0x4E
  | .ordinaryShares => 0x4F
  | .preferredStock => 0x50
  | .otherSecurities => 0x51
  | .rights => 0x52
  | .sharesOfBeneficialInterest => 0x53
  | .convertibleDebenture => 0x54
  | .unit => 0x55
  | .unitsOfBeneficialInterest => 0x56
  | .warrant => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IssueType :=
  if byte = 0x41 then .americanDepositoryReceipt
  else if byte = 0x42 then .bond
  else if byte = 0x43 then .commonStock
  else if byte = 0x46 then .depositoryReceipt
  else if byte = 0x49 then .rule144a
  else if byte = 0x4C then .limitedPartnership
  else if byte = 0x4E then .note
  else if byte = 0x4F then .ordinaryShares
  else if byte = 0x50 then .preferredStock
  else if byte = 0x51 then .otherSecurities
  else if byte = 0x52 then .rights
  else if byte = 0x53 then .sharesOfBeneficialInterest
  else if byte = 0x54 then .convertibleDebenture
  else if byte = 0x55 then .unit
  else if byte = 0x56 then .unitsOfBeneficialInterest
  else .warrant

def ofByte (byte : UInt8) : IssueType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IssueType) : ofByte value.toByte = value := by
  cases value with
  | americanDepositoryReceipt => decide
  | bond => decide
  | commonStock => decide
  | depositoryReceipt => decide
  | rule144a => decide
  | limitedPartnership => decide
  | note => decide
  | ordinaryShares => decide
  | preferredStock => decide
  | otherSecurities => decide
  | rights => decide
  | sharesOfBeneficialInterest => decide
  | convertibleDebenture => decide
  | unit => decide
  | unitsOfBeneficialInterest => decide
  | warrant => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IssueType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IssueType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IssueType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IssueType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IssueType

/-- Market Tier: one byte code -/
def MarketTier.codes : List UInt8 :=
  [0x51, 0x47, 0x53]

inductive MarketTier where
  | nasdaqGlobalSelectMarket -- Nasdaq Global Select Market
  | nasdaqGlobalMarket -- Nasdaq Global Market
  | nasdaqCapitalMarket -- Nasdaq Capital Market
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketTier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketTier

def toByte : MarketTier → UInt8
  | .nasdaqGlobalSelectMarket => 0x51
  | .nasdaqGlobalMarket => 0x47
  | .nasdaqCapitalMarket => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketTier :=
  if byte = 0x51 then .nasdaqGlobalSelectMarket
  else if byte = 0x47 then .nasdaqGlobalMarket
  else .nasdaqCapitalMarket

def ofByte (byte : UInt8) : MarketTier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketTier) : ofByte value.toByte = value := by
  cases value with
  | nasdaqGlobalSelectMarket => decide
  | nasdaqGlobalMarket => decide
  | nasdaqCapitalMarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketTier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketTier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketTier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketTier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketTier

/-- Authenticity: one byte code -/
def Authenticity.codes : List UInt8 :=
  [0x50, 0x54, 0x44, 0x58]

inductive Authenticity where
  | production -- Production
  | test -- Test
  | demo -- Demo
  | deleted -- Deleted
  | unlisted (byte : { byte : UInt8 // byte ∉ Authenticity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Authenticity

def toByte : Authenticity → UInt8
  | .production => 0x50
  | .test => 0x54
  | .demo => 0x44
  | .deleted => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Authenticity :=
  if byte = 0x50 then .production
  else if byte = 0x54 then .test
  else if byte = 0x44 then .demo
  else .deleted

def ofByte (byte : UInt8) : Authenticity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Authenticity) : ofByte value.toByte = value := by
  cases value with
  | production => decide
  | test => decide
  | demo => decide
  | deleted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Authenticity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Authenticity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Authenticity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Authenticity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Authenticity

/-- Short Sale Threshold Indicator: one byte code -/
def ShortSaleThresholdIndicator.codes : List UInt8 :=
  [0x59, 0x4E, 0x20]

inductive ShortSaleThresholdIndicator where
  | issueIsRestricted -- Issue Is Restricted
  | issueIsNotRestricted -- Issue Is Not Restricted
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSaleThresholdIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSaleThresholdIndicator

def toByte : ShortSaleThresholdIndicator → UInt8
  | .issueIsRestricted => 0x59
  | .issueIsNotRestricted => 0x4E
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSaleThresholdIndicator :=
  if byte = 0x59 then .issueIsRestricted
  else if byte = 0x4E then .issueIsNotRestricted
  else .notAvailable

def ofByte (byte : UInt8) : ShortSaleThresholdIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSaleThresholdIndicator) : ofByte value.toByte = value := by
  cases value with
  | issueIsRestricted => decide
  | issueIsNotRestricted => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSaleThresholdIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSaleThresholdIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSaleThresholdIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ShortSaleThresholdIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSaleThresholdIndicator

/-- Financial Status Indicator: one byte code -/
def FinancialStatusIndicator.codes : List UInt8 :=
  [0x43, 0x44, 0x45, 0x51, 0x4E, 0x47, 0x48, 0x4A, 0x4B]

inductive FinancialStatusIndicator where
  | creationsAndOrRedemptionsSuspended -- Creations And Or Redemptions Suspended
  | deficient -- Deficient
  | delinquent -- Delinquent
  | bankrupt -- Bankrupt
  | normal -- Normal
  | deficientAndBankrupt -- Deficient And Bankrupt
  | deficientAndDelinquent -- Deficient And Delinquent
  | delinquentAndBankrupt -- Delinquent And Bankrupt
  | deficientDelinquentAndBankrupt -- Deficient Delinquent And Bankrupt
  | unlisted (byte : { byte : UInt8 // byte ∉ FinancialStatusIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinancialStatusIndicator

def toByte : FinancialStatusIndicator → UInt8
  | .creationsAndOrRedemptionsSuspended => 0x43
  | .deficient => 0x44
  | .delinquent => 0x45
  | .bankrupt => 0x51
  | .normal => 0x4E
  | .deficientAndBankrupt => 0x47
  | .deficientAndDelinquent => 0x48
  | .delinquentAndBankrupt => 0x4A
  | .deficientDelinquentAndBankrupt => 0x4B
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinancialStatusIndicator :=
  if byte = 0x43 then .creationsAndOrRedemptionsSuspended
  else if byte = 0x44 then .deficient
  else if byte = 0x45 then .delinquent
  else if byte = 0x51 then .bankrupt
  else if byte = 0x4E then .normal
  else if byte = 0x47 then .deficientAndBankrupt
  else if byte = 0x48 then .deficientAndDelinquent
  else if byte = 0x4A then .delinquentAndBankrupt
  else .deficientDelinquentAndBankrupt

def ofByte (byte : UInt8) : FinancialStatusIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinancialStatusIndicator) : ofByte value.toByte = value := by
  cases value with
  | creationsAndOrRedemptionsSuspended => decide
  | deficient => decide
  | delinquent => decide
  | bankrupt => decide
  | normal => decide
  | deficientAndBankrupt => decide
  | deficientAndDelinquent => decide
  | delinquentAndBankrupt => decide
  | deficientDelinquentAndBankrupt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FinancialStatusIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinancialStatusIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FinancialStatusIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FinancialStatusIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FinancialStatusIndicator

/-- Reg Sho Action: one byte code -/
def RegShoAction.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive RegShoAction where
  | noPriceTestInEffect -- No Price Test In Effect
  | regShoInEffectDueToAnIntraDayPriceDrop -- Reg Sho In Effect Due To An Intra Day Price Drop
  | regShoRestrictionRemainsInEffect -- Reg Sho Restriction Remains In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ RegShoAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RegShoAction

def toByte : RegShoAction → UInt8
  | .noPriceTestInEffect => 0x30
  | .regShoInEffectDueToAnIntraDayPriceDrop => 0x31
  | .regShoRestrictionRemainsInEffect => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RegShoAction :=
  if byte = 0x30 then .noPriceTestInEffect
  else if byte = 0x31 then .regShoInEffectDueToAnIntraDayPriceDrop
  else .regShoRestrictionRemainsInEffect

def ofByte (byte : UInt8) : RegShoAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RegShoAction) : ofByte value.toByte = value := by
  cases value with
  | noPriceTestInEffect => decide
  | regShoInEffectDueToAnIntraDayPriceDrop => decide
  | regShoRestrictionRemainsInEffect => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RegShoAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RegShoAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RegShoAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RegShoAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RegShoAction

/-- Luld Price Band Indicator: one byte code -/
def LuldPriceBandIndicator.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x20]

inductive LuldPriceBandIndicator where
  | openingUpdate -- Opening Update
  | intraDayUpdate -- Intra Day Update
  | restatedValue -- Restated Value
  | suspendedDuringTradingHaltOrTradingPause -- Suspended During Trading Halt Or Trading Pause
  | reOpeningUpdate -- Re Opening Update
  | outsidePriceBandRuleHours -- Outside Price Band Rule Hours
  | noneProvided -- None Provided
  | unlisted (byte : { byte : UInt8 // byte ∉ LuldPriceBandIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LuldPriceBandIndicator

def toByte : LuldPriceBandIndicator → UInt8
  | .openingUpdate => 0x41
  | .intraDayUpdate => 0x42
  | .restatedValue => 0x43
  | .suspendedDuringTradingHaltOrTradingPause => 0x44
  | .reOpeningUpdate => 0x45
  | .outsidePriceBandRuleHours => 0x46
  | .noneProvided => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LuldPriceBandIndicator :=
  if byte = 0x41 then .openingUpdate
  else if byte = 0x42 then .intraDayUpdate
  else if byte = 0x43 then .restatedValue
  else if byte = 0x44 then .suspendedDuringTradingHaltOrTradingPause
  else if byte = 0x45 then .reOpeningUpdate
  else if byte = 0x46 then .outsidePriceBandRuleHours
  else .noneProvided

def ofByte (byte : UInt8) : LuldPriceBandIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LuldPriceBandIndicator) : ofByte value.toByte = value := by
  cases value with
  | openingUpdate => decide
  | intraDayUpdate => decide
  | restatedValue => decide
  | suspendedDuringTradingHaltOrTradingPause => decide
  | reOpeningUpdate => decide
  | outsidePriceBandRuleHours => decide
  | noneProvided => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LuldPriceBandIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LuldPriceBandIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LuldPriceBandIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LuldPriceBandIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LuldPriceBandIndicator

/-- Mwcb Status Level Indicator: one byte code -/
def MwcbStatusLevelIndicator.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive MwcbStatusLevelIndicator where
  | level1Breached -- Level 1 Breached
  | level2Breached -- Level 2 Breached
  | level3Breached -- Level 3 Breached
  | unlisted (byte : { byte : UInt8 // byte ∉ MwcbStatusLevelIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MwcbStatusLevelIndicator

def toByte : MwcbStatusLevelIndicator → UInt8
  | .level1Breached => 0x31
  | .level2Breached => 0x32
  | .level3Breached => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MwcbStatusLevelIndicator :=
  if byte = 0x31 then .level1Breached
  else if byte = 0x32 then .level2Breached
  else .level3Breached

def ofByte (byte : UInt8) : MwcbStatusLevelIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MwcbStatusLevelIndicator) : ofByte value.toByte = value := by
  cases value with
  | level1Breached => decide
  | level2Breached => decide
  | level3Breached => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MwcbStatusLevelIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MwcbStatusLevelIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MwcbStatusLevelIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MwcbStatusLevelIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MwcbStatusLevelIndicator

/-- Special Condition: one byte code -/
def SpecialCondition.codes : List UInt8 :=
  [0x4F, 0x48, 0x4D, 0x20]

inductive SpecialCondition where
  | oneSidedNationalBboAtMarketClose -- One Sided National Bbo At Market Close
  | tradingHaltInEffectAtMarketClose -- Trading Halt In Effect At Market Close
  | noEligibleMarketParticipantQuotesInIssueAtMarketClose -- No Eligible Market Participant Quotes In Issue At Market Close
  | noSpecialConditionExists -- No Special Condition Exists
  | unlisted (byte : { byte : UInt8 // byte ∉ SpecialCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SpecialCondition

def toByte : SpecialCondition → UInt8
  | .oneSidedNationalBboAtMarketClose => 0x4F
  | .tradingHaltInEffectAtMarketClose => 0x48
  | .noEligibleMarketParticipantQuotesInIssueAtMarketClose => 0x4D
  | .noSpecialConditionExists => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SpecialCondition :=
  if byte = 0x4F then .oneSidedNationalBboAtMarketClose
  else if byte = 0x48 then .tradingHaltInEffectAtMarketClose
  else if byte = 0x4D then .noEligibleMarketParticipantQuotesInIssueAtMarketClose
  else .noSpecialConditionExists

def ofByte (byte : UInt8) : SpecialCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SpecialCondition) : ofByte value.toByte = value := by
  cases value with
  | oneSidedNationalBboAtMarketClose => decide
  | tradingHaltInEffectAtMarketClose => decide
  | noEligibleMarketParticipantQuotesInIssueAtMarketClose => decide
  | noSpecialConditionExists => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SpecialCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SpecialCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SpecialCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SpecialCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SpecialCondition

/-- Message Info: 26 bytes -/
structure MessageInfo where
  marketCenterOriginatorId : MarketCenterOriginatorId
  subMarketCenterId : SubMarketCenterId
  sipTimestamp : BitVec 64
  participantTimestamp : BitVec 64
  participantToken : BitVec 64
  deriving DecidableEq, Repr

namespace MessageInfo

def encode (message : MessageInfo) : List UInt8 :=
  MarketCenterOriginatorId.encode message.marketCenterOriginatorId
    ++ (SubMarketCenterId.encode message.subMarketCenterId
    ++ (encodeUInt 8 message.sipTimestamp
    ++ (encodeUInt 8 message.participantTimestamp
    ++ (encodeUInt 8 message.participantToken))))

def decode (bytes : List UInt8) : Option (MessageInfo × List UInt8) := do
  let (marketCenterOriginatorId, bytes) ← MarketCenterOriginatorId.decode bytes
  let (subMarketCenterId, bytes) ← SubMarketCenterId.decode bytes
  let (sipTimestamp, bytes) ← decodeUInt 8 bytes
  let (participantTimestamp, bytes) ← decodeUInt 8 bytes
  let (participantToken, bytes) ← decodeUInt 8 bytes
  pure ({ marketCenterOriginatorId, subMarketCenterId, sipTimestamp, participantTimestamp, participantToken }, bytes)

@[simp] theorem encode_length (message : MessageInfo) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, MarketCenterOriginatorId.encode_length, SubMarketCenterId.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MessageInfo) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageInfo) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketCenterOriginatorId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SubMarketCenterId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MessageInfo

/-- Short Form National Bbo Appendage: 11 bytes -/
structure ShortFormNationalBboAppendage where
  nbboQuoteCondition : NbboQuoteCondition
  nationalBestBidMarketCenter : Alpha 1
  nationalBestBidPriceShort : BitVec 16
  nationalBestBidSizeShort : BitVec 16
  nationalBestAskMarketCenter : Alpha 1
  nationalBestAskPriceShort : BitVec 16
  nationalBestAskSizeShort : BitVec 16
  deriving DecidableEq, Repr

namespace ShortFormNationalBboAppendage

def encode (message : ShortFormNationalBboAppendage) : List UInt8 :=
  NbboQuoteCondition.encode message.nbboQuoteCondition
    ++ (Alpha.encode message.nationalBestBidMarketCenter
    ++ (encodeUInt 2 message.nationalBestBidPriceShort
    ++ (encodeUInt 2 message.nationalBestBidSizeShort
    ++ (Alpha.encode message.nationalBestAskMarketCenter
    ++ (encodeUInt 2 message.nationalBestAskPriceShort
    ++ (encodeUInt 2 message.nationalBestAskSizeShort))))))

def decode (bytes : List UInt8) : Option (ShortFormNationalBboAppendage × List UInt8) := do
  let (nbboQuoteCondition, bytes) ← NbboQuoteCondition.decode bytes
  let (nationalBestBidMarketCenter, bytes) ← Alpha.decode 1 bytes
  let (nationalBestBidPriceShort, bytes) ← decodeUInt 2 bytes
  let (nationalBestBidSizeShort, bytes) ← decodeUInt 2 bytes
  let (nationalBestAskMarketCenter, bytes) ← Alpha.decode 1 bytes
  let (nationalBestAskPriceShort, bytes) ← decodeUInt 2 bytes
  let (nationalBestAskSizeShort, bytes) ← decodeUInt 2 bytes
  pure ({ nbboQuoteCondition, nationalBestBidMarketCenter, nationalBestBidPriceShort, nationalBestBidSizeShort, nationalBestAskMarketCenter, nationalBestAskPriceShort, nationalBestAskSizeShort }, bytes)

@[simp] theorem encode_length (message : ShortFormNationalBboAppendage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, NbboQuoteCondition.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ShortFormNationalBboAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortFormNationalBboAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, NbboQuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

end ShortFormNationalBboAppendage

/-- Long Form National Bbo Appendage: 27 bytes -/
structure LongFormNationalBboAppendage where
  nbboQuoteCondition : NbboQuoteCondition
  bestBidMarketCenter : Alpha 1
  bestBidPrice : BitVec 64
  bestBidSize : BitVec 32
  bestAskMarketCenter : Alpha 1
  bestAskPrice : BitVec 64
  bestAskSize : BitVec 32
  deriving DecidableEq, Repr

namespace LongFormNationalBboAppendage

def encode (message : LongFormNationalBboAppendage) : List UInt8 :=
  NbboQuoteCondition.encode message.nbboQuoteCondition
    ++ (Alpha.encode message.bestBidMarketCenter
    ++ (encodeUInt 8 message.bestBidPrice
    ++ (encodeUInt 4 message.bestBidSize
    ++ (Alpha.encode message.bestAskMarketCenter
    ++ (encodeUInt 8 message.bestAskPrice
    ++ (encodeUInt 4 message.bestAskSize))))))

def decode (bytes : List UInt8) : Option (LongFormNationalBboAppendage × List UInt8) := do
  let (nbboQuoteCondition, bytes) ← NbboQuoteCondition.decode bytes
  let (bestBidMarketCenter, bytes) ← Alpha.decode 1 bytes
  let (bestBidPrice, bytes) ← decodeUInt 8 bytes
  let (bestBidSize, bytes) ← decodeUInt 4 bytes
  let (bestAskMarketCenter, bytes) ← Alpha.decode 1 bytes
  let (bestAskPrice, bytes) ← decodeUInt 8 bytes
  let (bestAskSize, bytes) ← decodeUInt 4 bytes
  pure ({ nbboQuoteCondition, bestBidMarketCenter, bestBidPrice, bestBidSize, bestAskMarketCenter, bestAskPrice, bestAskSize }, bytes)

@[simp] theorem encode_length (message : LongFormNationalBboAppendage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, NbboQuoteCondition.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LongFormNationalBboAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongFormNationalBboAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, NbboQuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

end LongFormNationalBboAppendage

/-- Nbbo Appendage Indicator: 0 bytes -/
structure NbboAppendageAbsent where
  deriving DecidableEq, Repr

namespace NbboAppendageAbsent

def encode (_ : NbboAppendageAbsent) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (NbboAppendageAbsent × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : NbboAppendageAbsent) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : NbboAppendageAbsent) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end NbboAppendageAbsent

/-- The Short Form National Bbo Appendage or Long Form National Bbo Appendage the Nbbo Appendage Indicator says is attached, or none -/
inductive NbboAppendageChoice where
  | shortFormNationalBboAppendage (message : ShortFormNationalBboAppendage) -- '2' 0x32
  | longFormNationalBboAppendage (message : LongFormNationalBboAppendage) -- '3' 0x33
  | noNationalBboChange (message : NbboAppendageAbsent) -- '0' 0x30
  | noNationalBboCanBeCalculated (message : NbboAppendageAbsent) -- '1' 0x31
  | quoteContainsAllNationalBboInformation (message : NbboAppendageAbsent) -- '4' 0x34
  deriving DecidableEq, Repr

namespace NbboAppendageChoice

/-- The Nbbo Appendage Indicator each message is sent under -/
def tag : NbboAppendageChoice → BitVec 8
  | .shortFormNationalBboAppendage _ => 50
  | .longFormNationalBboAppendage _ => 51
  | .noNationalBboChange _ => 48
  | .noNationalBboCanBeCalculated _ => 49
  | .quoteContainsAllNationalBboInformation _ => 52

def encode : NbboAppendageChoice → List UInt8
  | .shortFormNationalBboAppendage message => ShortFormNationalBboAppendage.encode message
  | .longFormNationalBboAppendage message => LongFormNationalBboAppendage.encode message
  | .noNationalBboChange message => NbboAppendageAbsent.encode message
  | .noNationalBboCanBeCalculated message => NbboAppendageAbsent.encode message
  | .quoteContainsAllNationalBboInformation message => NbboAppendageAbsent.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : NbboAppendageChoice) : (encode message).length ≤ 27 := by
  cases message with
  | shortFormNationalBboAppendage inner =>
    simp only [encode, ShortFormNationalBboAppendage.encode_length]
    omega
  | longFormNationalBboAppendage inner =>
    simp only [encode, LongFormNationalBboAppendage.encode_length]
    omega
  | noNationalBboChange inner =>
    simp only [encode, NbboAppendageAbsent.encode_length]
    omega
  | noNationalBboCanBeCalculated inner =>
    simp only [encode, NbboAppendageAbsent.encode_length]
    omega
  | quoteContainsAllNationalBboInformation inner =>
    simp only [encode, NbboAppendageAbsent.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (NbboAppendageChoice × List UInt8) :=
  if tag = 50 then (ShortFormNationalBboAppendage.decode bytes).map fun (message, rest) => (.shortFormNationalBboAppendage message, rest)
  else if tag = 51 then (LongFormNationalBboAppendage.decode bytes).map fun (message, rest) => (.longFormNationalBboAppendage message, rest)
  else if tag = 48 then (NbboAppendageAbsent.decode bytes).map fun (message, rest) => (.noNationalBboChange message, rest)
  else if tag = 49 then (NbboAppendageAbsent.decode bytes).map fun (message, rest) => (.noNationalBboCanBeCalculated message, rest)
  else if tag = 52 then (NbboAppendageAbsent.decode bytes).map fun (message, rest) => (.quoteContainsAllNationalBboInformation message, rest)
  else none

@[simp] theorem decode_encode (message : NbboAppendageChoice) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end NbboAppendageChoice

/-- Quote Short Form Message -/
structure QuoteShortFormMessage where
  messageInfo : MessageInfo
  symbolShort : Alpha 5
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  askPriceShort : BitVec 16
  askSizeShort : BitVec 16
  quoteCondition : QuoteCondition
  sipGeneratedUpdate : SipGeneratedUpdate
  luldBboIndicator : LuldBboIndicator
  retailInterestIndicator : RetailInterestIndicator
  luldNationalBboIndicator : LuldNationalBboIndicator
  nbboAppendageChoice : NbboAppendageChoice
  deriving DecidableEq, Repr

namespace QuoteShortFormMessage

def encode (message : QuoteShortFormMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolShort
    ++ (encodeUInt 2 message.bidPriceShort
    ++ (encodeUInt 2 message.bidSizeShort
    ++ (encodeUInt 2 message.askPriceShort
    ++ (encodeUInt 2 message.askSizeShort
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (SipGeneratedUpdate.encode message.sipGeneratedUpdate
    ++ (LuldBboIndicator.encode message.luldBboIndicator
    ++ (RetailInterestIndicator.encode message.retailInterestIndicator
    ++ (encodeUInt 1 (NbboAppendageChoice.tag message.nbboAppendageChoice)
    ++ (LuldNationalBboIndicator.encode message.luldNationalBboIndicator
    ++ (NbboAppendageChoice.encode message.nbboAppendageChoice))))))))))))

def decode (bytes : List UInt8) : Option (QuoteShortFormMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolShort, bytes) ← Alpha.decode 5 bytes
  let (bidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bidSizeShort, bytes) ← decodeUInt 2 bytes
  let (askPriceShort, bytes) ← decodeUInt 2 bytes
  let (askSizeShort, bytes) ← decodeUInt 2 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (sipGeneratedUpdate, bytes) ← SipGeneratedUpdate.decode bytes
  let (luldBboIndicator, bytes) ← LuldBboIndicator.decode bytes
  let (retailInterestIndicator, bytes) ← RetailInterestIndicator.decode bytes
  let (nbboAppendageIndicator, bytes) ← decodeUInt 1 bytes
  let (luldNationalBboIndicator, bytes) ← LuldNationalBboIndicator.decode bytes
  let (nbboAppendageChoice, bytes) ← NbboAppendageChoice.decode nbboAppendageIndicator bytes
  pure ({ messageInfo, symbolShort, bidPriceShort, bidSizeShort, askPriceShort, askSizeShort, quoteCondition, sipGeneratedUpdate, luldBboIndicator, retailInterestIndicator, luldNationalBboIndicator, nbboAppendageChoice }, bytes)

theorem encode_length_pos (message : QuoteShortFormMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [MessageInfo.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteShortFormMessage) : (encode message).length ≤ 72 := by
  unfold encode
  cases message.nbboAppendageChoice with
  | shortFormNationalBboAppendage inner =>
    simp only [NbboAppendageChoice.encode, List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, Alpha.encode_length, encodeUInt_length, QuoteCondition.encode_length, SipGeneratedUpdate.encode_length, LuldBboIndicator.encode_length, RetailInterestIndicator.encode_length, LuldNationalBboIndicator.encode_length, ShortFormNationalBboAppendage.encode_length]
    omega
  | longFormNationalBboAppendage inner =>
    simp only [NbboAppendageChoice.encode, List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, Alpha.encode_length, encodeUInt_length, QuoteCondition.encode_length, SipGeneratedUpdate.encode_length, LuldBboIndicator.encode_length, RetailInterestIndicator.encode_length, LuldNationalBboIndicator.encode_length, LongFormNationalBboAppendage.encode_length]
    omega
  | noNationalBboChange inner =>
    simp only [NbboAppendageChoice.encode, List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, Alpha.encode_length, encodeUInt_length, QuoteCondition.encode_length, SipGeneratedUpdate.encode_length, LuldBboIndicator.encode_length, RetailInterestIndicator.encode_length, LuldNationalBboIndicator.encode_length, NbboAppendageAbsent.encode_length]
    omega
  | noNationalBboCanBeCalculated inner =>
    simp only [NbboAppendageChoice.encode, List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, Alpha.encode_length, encodeUInt_length, QuoteCondition.encode_length, SipGeneratedUpdate.encode_length, LuldBboIndicator.encode_length, RetailInterestIndicator.encode_length, LuldNationalBboIndicator.encode_length, NbboAppendageAbsent.encode_length]
    omega
  | quoteContainsAllNationalBboInformation inner =>
    simp only [NbboAppendageChoice.encode, List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, Alpha.encode_length, encodeUInt_length, QuoteCondition.encode_length, SipGeneratedUpdate.encode_length, LuldBboIndicator.encode_length, RetailInterestIndicator.encode_length, LuldNationalBboIndicator.encode_length, NbboAppendageAbsent.encode_length]
    omega

@[simp] theorem decode_encode (message : QuoteShortFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
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
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SipGeneratedUpdate.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LuldBboIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RetailInterestIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LuldNationalBboIndicator.decode_encode, some_bind]
  dsimp only
  rw [NbboAppendageChoice.decode_encode, some_bind]
  rfl

end QuoteShortFormMessage

/-- Finra Adf Mpid Appendage: 8 bytes -/
structure FinraAdfMpidAppendage where
  bidAdfMpid : Alpha 4
  askAdfMpid : Alpha 4
  deriving DecidableEq, Repr

namespace FinraAdfMpidAppendage

def encode (message : FinraAdfMpidAppendage) : List UInt8 :=
  Alpha.encode message.bidAdfMpid
    ++ (Alpha.encode message.askAdfMpid)

def decode (bytes : List UInt8) : Option (FinraAdfMpidAppendage × List UInt8) := do
  let (bidAdfMpid, bytes) ← Alpha.decode 4 bytes
  let (askAdfMpid, bytes) ← Alpha.decode 4 bytes
  pure ({ bidAdfMpid, askAdfMpid }, bytes)

@[simp] theorem encode_length (message : FinraAdfMpidAppendage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : FinraAdfMpidAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FinraAdfMpidAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FinraAdfMpidAppendage

/-- Finra Adf Mpid Appendage Indicator: 0 bytes -/
structure FinraAdfMpidAppendageAbsent where
  deriving DecidableEq, Repr

namespace FinraAdfMpidAppendageAbsent

def encode (_ : FinraAdfMpidAppendageAbsent) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (FinraAdfMpidAppendageAbsent × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : FinraAdfMpidAppendageAbsent) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : FinraAdfMpidAppendageAbsent) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end FinraAdfMpidAppendageAbsent

/-- The Finra Adf Mpid Appendage the Finra Adf Mpid Appendage Indicator says is attached, or none -/
inductive FinraAdfMpidAppendageChoice where
  | finraAdfMpidAppendage (message : FinraAdfMpidAppendage) -- '2' 0x32
  | notApplicable (message : FinraAdfMpidAppendageAbsent) -- ' ' 0x20
  | noAdfMpidChanges (message : FinraAdfMpidAppendageAbsent) -- '0' 0x30
  | noAdfMpidExists (message : FinraAdfMpidAppendageAbsent) -- '1' 0x31
  deriving DecidableEq, Repr

namespace FinraAdfMpidAppendageChoice

/-- The Finra Adf Mpid Appendage Indicator each message is sent under -/
def tag : FinraAdfMpidAppendageChoice → BitVec 8
  | .finraAdfMpidAppendage _ => 50
  | .notApplicable _ => 32
  | .noAdfMpidChanges _ => 48
  | .noAdfMpidExists _ => 49

def encode : FinraAdfMpidAppendageChoice → List UInt8
  | .finraAdfMpidAppendage message => FinraAdfMpidAppendage.encode message
  | .notApplicable message => FinraAdfMpidAppendageAbsent.encode message
  | .noAdfMpidChanges message => FinraAdfMpidAppendageAbsent.encode message
  | .noAdfMpidExists message => FinraAdfMpidAppendageAbsent.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : FinraAdfMpidAppendageChoice) : (encode message).length ≤ 8 := by
  cases message with
  | finraAdfMpidAppendage inner =>
    simp only [encode, FinraAdfMpidAppendage.encode_length]
    omega
  | notApplicable inner =>
    simp only [encode, FinraAdfMpidAppendageAbsent.encode_length]
    omega
  | noAdfMpidChanges inner =>
    simp only [encode, FinraAdfMpidAppendageAbsent.encode_length]
    omega
  | noAdfMpidExists inner =>
    simp only [encode, FinraAdfMpidAppendageAbsent.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (FinraAdfMpidAppendageChoice × List UInt8) :=
  if tag = 50 then (FinraAdfMpidAppendage.decode bytes).map fun (message, rest) => (.finraAdfMpidAppendage message, rest)
  else if tag = 32 then (FinraAdfMpidAppendageAbsent.decode bytes).map fun (message, rest) => (.notApplicable message, rest)
  else if tag = 48 then (FinraAdfMpidAppendageAbsent.decode bytes).map fun (message, rest) => (.noAdfMpidChanges message, rest)
  else if tag = 49 then (FinraAdfMpidAppendageAbsent.decode bytes).map fun (message, rest) => (.noAdfMpidExists message, rest)
  else none

@[simp] theorem decode_encode (message : FinraAdfMpidAppendageChoice) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end FinraAdfMpidAppendageChoice

/-- Quote Long Form Message -/
structure QuoteLongFormMessage where
  messageInfo : MessageInfo
  finraTimestamp : BitVec 64
  symbolLong : Alpha 11
  bidPrice : BitVec 64
  bidSize : BitVec 32
  askPrice : BitVec 64
  askSize : BitVec 32
  quoteCondition : QuoteCondition
  sipGeneratedUpdate : SipGeneratedUpdate
  luldBboIndicator : LuldBboIndicator
  retailInterestIndicator : RetailInterestIndicator
  luldNationalBboIndicator : LuldNationalBboIndicator
  nbboAppendageChoice : NbboAppendageChoice
  finraAdfMpidAppendageChoice : FinraAdfMpidAppendageChoice
  deriving DecidableEq, Repr

namespace QuoteLongFormMessage

def encode (message : QuoteLongFormMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (encodeUInt 8 message.finraTimestamp
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 8 message.bidPrice
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 8 message.askPrice
    ++ (encodeUInt 4 message.askSize
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (SipGeneratedUpdate.encode message.sipGeneratedUpdate
    ++ (LuldBboIndicator.encode message.luldBboIndicator
    ++ (RetailInterestIndicator.encode message.retailInterestIndicator
    ++ (encodeUInt 1 (NbboAppendageChoice.tag message.nbboAppendageChoice)
    ++ (LuldNationalBboIndicator.encode message.luldNationalBboIndicator
    ++ (encodeUInt 1 (FinraAdfMpidAppendageChoice.tag message.finraAdfMpidAppendageChoice)
    ++ (NbboAppendageChoice.encode message.nbboAppendageChoice
    ++ (FinraAdfMpidAppendageChoice.encode message.finraAdfMpidAppendageChoice)))))))))))))))

def decode (bytes : List UInt8) : Option (QuoteLongFormMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (finraTimestamp, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (bidPrice, bytes) ← decodeUInt 8 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (askPrice, bytes) ← decodeUInt 8 bytes
  let (askSize, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (sipGeneratedUpdate, bytes) ← SipGeneratedUpdate.decode bytes
  let (luldBboIndicator, bytes) ← LuldBboIndicator.decode bytes
  let (retailInterestIndicator, bytes) ← RetailInterestIndicator.decode bytes
  let (nbboAppendageIndicator, bytes) ← decodeUInt 1 bytes
  let (luldNationalBboIndicator, bytes) ← LuldNationalBboIndicator.decode bytes
  let (finraAdfMpidAppendageIndicator, bytes) ← decodeUInt 1 bytes
  let (nbboAppendageChoice, bytes) ← NbboAppendageChoice.decode nbboAppendageIndicator bytes
  let (finraAdfMpidAppendageChoice, bytes) ← FinraAdfMpidAppendageChoice.decode finraAdfMpidAppendageIndicator bytes
  pure ({ messageInfo, finraTimestamp, symbolLong, bidPrice, bidSize, askPrice, askSize, quoteCondition, sipGeneratedUpdate, luldBboIndicator, retailInterestIndicator, luldNationalBboIndicator, nbboAppendageChoice, finraAdfMpidAppendageChoice }, bytes)

theorem encode_length_pos (message : QuoteLongFormMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [MessageInfo.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteLongFormMessage) : (encode message).length ≤ 111 := by
  have bound_finraAdfMpidAppendageChoice := FinraAdfMpidAppendageChoice.encode_length_le message.finraAdfMpidAppendageChoice
  unfold encode
  cases message.nbboAppendageChoice with
  | shortFormNationalBboAppendage inner =>
    simp only [NbboAppendageChoice.encode, List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, encodeUInt_length, Alpha.encode_length, QuoteCondition.encode_length, SipGeneratedUpdate.encode_length, LuldBboIndicator.encode_length, RetailInterestIndicator.encode_length, LuldNationalBboIndicator.encode_length, ShortFormNationalBboAppendage.encode_length]
    omega
  | longFormNationalBboAppendage inner =>
    simp only [NbboAppendageChoice.encode, List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, encodeUInt_length, Alpha.encode_length, QuoteCondition.encode_length, SipGeneratedUpdate.encode_length, LuldBboIndicator.encode_length, RetailInterestIndicator.encode_length, LuldNationalBboIndicator.encode_length, LongFormNationalBboAppendage.encode_length]
    omega
  | noNationalBboChange inner =>
    simp only [NbboAppendageChoice.encode, List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, encodeUInt_length, Alpha.encode_length, QuoteCondition.encode_length, SipGeneratedUpdate.encode_length, LuldBboIndicator.encode_length, RetailInterestIndicator.encode_length, LuldNationalBboIndicator.encode_length, NbboAppendageAbsent.encode_length]
    omega
  | noNationalBboCanBeCalculated inner =>
    simp only [NbboAppendageChoice.encode, List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, encodeUInt_length, Alpha.encode_length, QuoteCondition.encode_length, SipGeneratedUpdate.encode_length, LuldBboIndicator.encode_length, RetailInterestIndicator.encode_length, LuldNationalBboIndicator.encode_length, NbboAppendageAbsent.encode_length]
    omega
  | quoteContainsAllNationalBboInformation inner =>
    simp only [NbboAppendageChoice.encode, List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, encodeUInt_length, Alpha.encode_length, QuoteCondition.encode_length, SipGeneratedUpdate.encode_length, LuldBboIndicator.encode_length, RetailInterestIndicator.encode_length, LuldNationalBboIndicator.encode_length, NbboAppendageAbsent.encode_length]
    omega

@[simp] theorem decode_encode (message : QuoteLongFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
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
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SipGeneratedUpdate.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LuldBboIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RetailInterestIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LuldNationalBboIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, NbboAppendageChoice.decode_encode, some_bind]
  dsimp only
  rw [FinraAdfMpidAppendageChoice.decode_encode, some_bind]
  rfl

end QuoteLongFormMessage

/-- Finra Adf Market Participant Quotation Message: 74 bytes -/
structure FinraAdfMarketParticipantQuotationMessage where
  messageInfo : MessageInfo
  finraTimestamp : BitVec 64
  symbolLong : Alpha 11
  bidPrice : BitVec 64
  bidSize : BitVec 32
  askPrice : BitVec 64
  askSize : BitVec 32
  quoteCondition : QuoteCondition
  finraMarketParticipant : Alpha 4
  deriving DecidableEq, Repr

namespace FinraAdfMarketParticipantQuotationMessage

def encode (message : FinraAdfMarketParticipantQuotationMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (encodeUInt 8 message.finraTimestamp
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 8 message.bidPrice
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 8 message.askPrice
    ++ (encodeUInt 4 message.askSize
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.finraMarketParticipant))))))))

def decode (bytes : List UInt8) : Option (FinraAdfMarketParticipantQuotationMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (finraTimestamp, bytes) ← decodeUInt 8 bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (bidPrice, bytes) ← decodeUInt 8 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (askPrice, bytes) ← decodeUInt 8 bytes
  let (askSize, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (finraMarketParticipant, bytes) ← Alpha.decode 4 bytes
  pure ({ messageInfo, finraTimestamp, symbolLong, bidPrice, bidSize, askPrice, askSize, quoteCondition, finraMarketParticipant }, bytes)

@[simp] theorem encode_length (message : FinraAdfMarketParticipantQuotationMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, encodeUInt_length, Alpha.encode_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : FinraAdfMarketParticipantQuotationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FinraAdfMarketParticipantQuotationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
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
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FinraAdfMarketParticipantQuotationMessage

/-- Any Quote Message Payload, selected by Quote Message Type -/
inductive QuoteMessagePayload where
  | quoteShortFormMessage (message : QuoteShortFormMessage) -- 'E' 0x45
  | quoteLongFormMessage (message : QuoteLongFormMessage) -- 'F' 0x46
  | finraAdfMarketParticipantQuotationMessage (message : FinraAdfMarketParticipantQuotationMessage) -- 'M' 0x4D
  deriving DecidableEq, Repr

namespace QuoteMessagePayload

/-- The Quote Message Type each message is sent under -/
def tag : QuoteMessagePayload → BitVec 8
  | .quoteShortFormMessage _ => 69
  | .quoteLongFormMessage _ => 70
  | .finraAdfMarketParticipantQuotationMessage _ => 77

def encode : QuoteMessagePayload → List UInt8
  | .quoteShortFormMessage message => QuoteShortFormMessage.encode message
  | .quoteLongFormMessage message => QuoteLongFormMessage.encode message
  | .finraAdfMarketParticipantQuotationMessage message => FinraAdfMarketParticipantQuotationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : QuoteMessagePayload) : (encode message).length ≤ 111 := by
  cases message with
  | quoteShortFormMessage inner =>
    have bound_inner := QuoteShortFormMessage.encode_length_le inner
    simp only [encode]
    omega
  | quoteLongFormMessage inner =>
    have bound_inner := QuoteLongFormMessage.encode_length_le inner
    simp only [encode]
    omega
  | finraAdfMarketParticipantQuotationMessage inner =>
    simp only [encode, FinraAdfMarketParticipantQuotationMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (QuoteMessagePayload × List UInt8) :=
  if tag = 69 then (QuoteShortFormMessage.decode bytes).map fun (message, rest) => (.quoteShortFormMessage message, rest)
  else if tag = 70 then (QuoteLongFormMessage.decode bytes).map fun (message, rest) => (.quoteLongFormMessage message, rest)
  else if tag = 77 then (FinraAdfMarketParticipantQuotationMessage.decode bytes).map fun (message, rest) => (.finraAdfMarketParticipantQuotationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : QuoteMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end QuoteMessagePayload

/-- Quote Message -/
structure QuoteMessage where
  quoteMessagePayload : QuoteMessagePayload
  deriving DecidableEq, Repr

namespace QuoteMessage

def encode (message : QuoteMessage) : List UInt8 :=
  encodeUInt 1 (QuoteMessagePayload.tag message.quoteMessagePayload)
    ++ (QuoteMessagePayload.encode message.quoteMessagePayload)

def decode (bytes : List UInt8) : Option (QuoteMessage × List UInt8) := do
  let (quoteMessageType, bytes) ← decodeUInt 1 bytes
  let (quoteMessagePayload, bytes) ← QuoteMessagePayload.decode quoteMessageType bytes
  pure ({ quoteMessagePayload }, bytes)

theorem encode_length_pos (message : QuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteMessage) : (encode message).length ≤ 112 := by
  unfold encode
  cases message.quoteMessagePayload with
  | quoteShortFormMessage inner =>
    have bound_inner := QuoteShortFormMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | quoteLongFormMessage inner =>
    have bound_inner := QuoteLongFormMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | finraAdfMarketParticipantQuotationMessage inner =>
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length, FinraAdfMarketParticipantQuotationMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : QuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [QuoteMessagePayload.decode_encode, some_bind]
  rfl

end QuoteMessage

/-- General Administrative Message -/
structure GeneralAdministrativeMessage where
  messageInfo : MessageInfo
  text : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace GeneralAdministrativeMessage

def encode (message : GeneralAdministrativeMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.text.val.length)
    ++ (encodeMany Byte.encode message.text.val))

def decode (bytes : List UInt8) : Option (GeneralAdministrativeMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (textLength, bytes) ← decodeUInt 2 bytes
  let (text_, bytes) ← decodeMany Byte.decode textLength.toNat bytes
  if fits_text : text_.length < 256 ^ 2 then
    pure ({ messageInfo, text := ⟨text_, fits_text⟩ }, bytes)
  else none

theorem encode_length_pos (message : GeneralAdministrativeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [MessageInfo.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GeneralAdministrativeMessage) : (encode message).length ≤ 65563 := by
  have bound_text := message.text.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : GeneralAdministrativeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.text.length_lt]
  rfl

end GeneralAdministrativeMessage

/-- Cross Sro Trading Action Message: 56 bytes -/
structure CrossSroTradingActionMessage where
  messageInfo : MessageInfo
  symbolLong : Alpha 11
  tradingActionCode : TradingActionCode
  tradingActionSequenceNumber : BitVec 32
  actionTimestamp : BitVec 64
  tradingActionReason : Alpha 6
  deriving DecidableEq, Repr

namespace CrossSroTradingActionMessage

def encode (message : CrossSroTradingActionMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolLong
    ++ (TradingActionCode.encode message.tradingActionCode
    ++ (encodeUInt 4 message.tradingActionSequenceNumber
    ++ (encodeUInt 8 message.actionTimestamp
    ++ (Alpha.encode message.tradingActionReason)))))

def decode (bytes : List UInt8) : Option (CrossSroTradingActionMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradingActionCode, bytes) ← TradingActionCode.decode bytes
  let (tradingActionSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (actionTimestamp, bytes) ← decodeUInt 8 bytes
  let (tradingActionReason, bytes) ← Alpha.decode 6 bytes
  pure ({ messageInfo, symbolLong, tradingActionCode, tradingActionSequenceNumber, actionTimestamp, tradingActionReason }, bytes)

@[simp] theorem encode_length (message : CrossSroTradingActionMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, Alpha.encode_length, TradingActionCode.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CrossSroTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossSroTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingActionCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CrossSroTradingActionMessage

/-- Market Center Trading Action Message: 47 bytes -/
structure MarketCenterTradingActionMessage where
  messageInfo : MessageInfo
  symbolLong : Alpha 11
  tradingActionCode : TradingActionCode
  actionTimestamp : BitVec 64
  marketCenterIdentifier : Alpha 1
  deriving DecidableEq, Repr

namespace MarketCenterTradingActionMessage

def encode (message : MarketCenterTradingActionMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolLong
    ++ (TradingActionCode.encode message.tradingActionCode
    ++ (encodeUInt 8 message.actionTimestamp
    ++ (Alpha.encode message.marketCenterIdentifier))))

def decode (bytes : List UInt8) : Option (MarketCenterTradingActionMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradingActionCode, bytes) ← TradingActionCode.decode bytes
  let (actionTimestamp, bytes) ← decodeUInt 8 bytes
  let (marketCenterIdentifier, bytes) ← Alpha.decode 1 bytes
  pure ({ messageInfo, symbolLong, tradingActionCode, actionTimestamp, marketCenterIdentifier }, bytes)

@[simp] theorem encode_length (message : MarketCenterTradingActionMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, Alpha.encode_length, TradingActionCode.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MarketCenterTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketCenterTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingActionCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketCenterTradingActionMessage

/-- Issue Symbol Directory Message: 87 bytes -/
structure IssueSymbolDirectoryMessage where
  messageInfo : MessageInfo
  symbolLong : Alpha 11
  oldSymbol : Alpha 11
  issueName : Alpha 30
  issueType : IssueType
  issueSubtype : Alpha 2
  marketTier : MarketTier
  authenticity : Authenticity
  shortSaleThresholdIndicator : ShortSaleThresholdIndicator
  roundLotSize : BitVec 16
  financialStatusIndicator : FinancialStatusIndicator
  deriving DecidableEq, Repr

namespace IssueSymbolDirectoryMessage

def encode (message : IssueSymbolDirectoryMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolLong
    ++ (Alpha.encode message.oldSymbol
    ++ (Alpha.encode message.issueName
    ++ (IssueType.encode message.issueType
    ++ (Alpha.encode message.issueSubtype
    ++ (MarketTier.encode message.marketTier
    ++ (Authenticity.encode message.authenticity
    ++ (ShortSaleThresholdIndicator.encode message.shortSaleThresholdIndicator
    ++ (encodeUInt 2 message.roundLotSize
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator))))))))))

def decode (bytes : List UInt8) : Option (IssueSymbolDirectoryMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (oldSymbol, bytes) ← Alpha.decode 11 bytes
  let (issueName, bytes) ← Alpha.decode 30 bytes
  let (issueType, bytes) ← IssueType.decode bytes
  let (issueSubtype, bytes) ← Alpha.decode 2 bytes
  let (marketTier, bytes) ← MarketTier.decode bytes
  let (authenticity, bytes) ← Authenticity.decode bytes
  let (shortSaleThresholdIndicator, bytes) ← ShortSaleThresholdIndicator.decode bytes
  let (roundLotSize, bytes) ← decodeUInt 2 bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  pure ({ messageInfo, symbolLong, oldSymbol, issueName, issueType, issueSubtype, marketTier, authenticity, shortSaleThresholdIndicator, roundLotSize, financialStatusIndicator }, bytes)

@[simp] theorem encode_length (message : IssueSymbolDirectoryMessage) : (encode message).length = 87 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, Alpha.encode_length, IssueType.encode_length, MarketTier.encode_length, Authenticity.encode_length, ShortSaleThresholdIndicator.encode_length, encodeUInt_length, FinancialStatusIndicator.encode_length]

theorem encode_length_pos (message : IssueSymbolDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueSymbolDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IssueType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketTier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Authenticity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleThresholdIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [FinancialStatusIndicator.decode_encode, some_bind]
  rfl

end IssueSymbolDirectoryMessage

/-- Regulation Sho Short Sale Price Test Restricted Indicator Message: 32 bytes -/
structure RegulationShoShortSalePriceTestRestrictedIndicatorMessage where
  messageInfo : MessageInfo
  symbolShort : Alpha 5
  regShoAction : RegShoAction
  deriving DecidableEq, Repr

namespace RegulationShoShortSalePriceTestRestrictedIndicatorMessage

def encode (message : RegulationShoShortSalePriceTestRestrictedIndicatorMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolShort
    ++ (RegShoAction.encode message.regShoAction))

def decode (bytes : List UInt8) : Option (RegulationShoShortSalePriceTestRestrictedIndicatorMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolShort, bytes) ← Alpha.decode 5 bytes
  let (regShoAction, bytes) ← RegShoAction.decode bytes
  pure ({ messageInfo, symbolShort, regShoAction }, bytes)

@[simp] theorem encode_length (message : RegulationShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, Alpha.encode_length, RegShoAction.encode_length]

theorem encode_length_pos (message : RegulationShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegulationShoShortSalePriceTestRestrictedIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RegShoAction.decode_encode, some_bind]
  rfl

end RegulationShoShortSalePriceTestRestrictedIndicatorMessage

/-- Limit Up Limit Down Price Band Message: 62 bytes -/
structure LimitUpLimitDownPriceBandMessage where
  messageInfo : MessageInfo
  symbolLong : Alpha 11
  luldPriceBandIndicator : LuldPriceBandIndicator
  luldTimestamp : BitVec 64
  limitDownPrice : BitVec 64
  limitUpPrice : BitVec 64
  deriving DecidableEq, Repr

namespace LimitUpLimitDownPriceBandMessage

def encode (message : LimitUpLimitDownPriceBandMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolLong
    ++ (LuldPriceBandIndicator.encode message.luldPriceBandIndicator
    ++ (encodeUInt 8 message.luldTimestamp
    ++ (encodeUInt 8 message.limitDownPrice
    ++ (encodeUInt 8 message.limitUpPrice)))))

def decode (bytes : List UInt8) : Option (LimitUpLimitDownPriceBandMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (luldPriceBandIndicator, bytes) ← LuldPriceBandIndicator.decode bytes
  let (luldTimestamp, bytes) ← decodeUInt 8 bytes
  let (limitDownPrice, bytes) ← decodeUInt 8 bytes
  let (limitUpPrice, bytes) ← decodeUInt 8 bytes
  pure ({ messageInfo, symbolLong, luldPriceBandIndicator, luldTimestamp, limitDownPrice, limitUpPrice }, bytes)

@[simp] theorem encode_length (message : LimitUpLimitDownPriceBandMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, Alpha.encode_length, LuldPriceBandIndicator.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LimitUpLimitDownPriceBandMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LimitUpLimitDownPriceBandMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LuldPriceBandIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LimitUpLimitDownPriceBandMessage

/-- Market Wide Circuit Breaker Decline Level Message: 50 bytes -/
structure MarketWideCircuitBreakerDeclineLevelMessage where
  messageInfo : MessageInfo
  mwcbLevel1 : BitVec 64
  mwcbLevel2 : BitVec 64
  mwcbLevel3 : BitVec 64
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerDeclineLevelMessage

def encode (message : MarketWideCircuitBreakerDeclineLevelMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (encodeUInt 8 message.mwcbLevel1
    ++ (encodeUInt 8 message.mwcbLevel2
    ++ (encodeUInt 8 message.mwcbLevel3)))

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerDeclineLevelMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (mwcbLevel1, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel2, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel3, bytes) ← decodeUInt 8 bytes
  pure ({ messageInfo, mwcbLevel1, mwcbLevel2, mwcbLevel3 }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerDeclineLevelMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MarketWideCircuitBreakerDeclineLevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketWideCircuitBreakerDeclineLevelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketWideCircuitBreakerDeclineLevelMessage

/-- Market Wide Circuit Breaker Status Message: 27 bytes -/
structure MarketWideCircuitBreakerStatusMessage where
  messageInfo : MessageInfo
  mwcbStatusLevelIndicator : MwcbStatusLevelIndicator
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerStatusMessage

def encode (message : MarketWideCircuitBreakerStatusMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (MwcbStatusLevelIndicator.encode message.mwcbStatusLevelIndicator)

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerStatusMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (mwcbStatusLevelIndicator, bytes) ← MwcbStatusLevelIndicator.decode bytes
  pure ({ messageInfo, mwcbStatusLevelIndicator }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerStatusMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, MwcbStatusLevelIndicator.encode_length]

theorem encode_length_pos (message : MarketWideCircuitBreakerStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketWideCircuitBreakerStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [MwcbStatusLevelIndicator.decode_encode, some_bind]
  rfl

end MarketWideCircuitBreakerStatusMessage

/-- Auction Collar Message: 66 bytes -/
structure AuctionCollarMessage where
  messageInfo : MessageInfo
  symbolLong : Alpha 11
  tradingActionSequenceNumber : BitVec 32
  collarReferencePrice : BitVec 64
  collarUpPrice : BitVec 64
  collarDownPrice : BitVec 64
  collarExtensionIndicator : Alpha 1
  deriving DecidableEq, Repr

namespace AuctionCollarMessage

def encode (message : AuctionCollarMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolLong
    ++ (encodeUInt 4 message.tradingActionSequenceNumber
    ++ (encodeUInt 8 message.collarReferencePrice
    ++ (encodeUInt 8 message.collarUpPrice
    ++ (encodeUInt 8 message.collarDownPrice
    ++ (Alpha.encode message.collarExtensionIndicator))))))

def decode (bytes : List UInt8) : Option (AuctionCollarMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (tradingActionSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (collarReferencePrice, bytes) ← decodeUInt 8 bytes
  let (collarUpPrice, bytes) ← decodeUInt 8 bytes
  let (collarDownPrice, bytes) ← decodeUInt 8 bytes
  let (collarExtensionIndicator, bytes) ← Alpha.decode 1 bytes
  pure ({ messageInfo, symbolLong, tradingActionSequenceNumber, collarReferencePrice, collarUpPrice, collarDownPrice, collarExtensionIndicator }, bytes)

@[simp] theorem encode_length (message : AuctionCollarMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, MessageInfo.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AuctionCollarMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionCollarMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end AuctionCollarMessage

/-- Market Center Close Recap: 33 bytes -/
structure MarketCenterCloseRecap where
  marketCenterIdentifier : Alpha 1
  marketCenterBidPrice : BitVec 64
  marketCenterBidSize : BitVec 64
  marketCenterAskPrice : BitVec 64
  marketCenterAskSize : BitVec 64
  deriving DecidableEq, Repr

namespace MarketCenterCloseRecap

def encode (message : MarketCenterCloseRecap) : List UInt8 :=
  Alpha.encode message.marketCenterIdentifier
    ++ (encodeUInt 8 message.marketCenterBidPrice
    ++ (encodeUInt 8 message.marketCenterBidSize
    ++ (encodeUInt 8 message.marketCenterAskPrice
    ++ (encodeUInt 8 message.marketCenterAskSize))))

def decode (bytes : List UInt8) : Option (MarketCenterCloseRecap × List UInt8) := do
  let (marketCenterIdentifier, bytes) ← Alpha.decode 1 bytes
  let (marketCenterBidPrice, bytes) ← decodeUInt 8 bytes
  let (marketCenterBidSize, bytes) ← decodeUInt 8 bytes
  let (marketCenterAskPrice, bytes) ← decodeUInt 8 bytes
  let (marketCenterAskSize, bytes) ← decodeUInt 8 bytes
  pure ({ marketCenterIdentifier, marketCenterBidPrice, marketCenterBidSize, marketCenterAskPrice, marketCenterAskSize }, bytes)

@[simp] theorem encode_length (message : MarketCenterCloseRecap) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MarketCenterCloseRecap) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketCenterCloseRecap) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketCenterCloseRecap

/-- Session Close Recap Message -/
structure SessionCloseRecapMessage where
  messageInfo : MessageInfo
  symbolLong : Alpha 11
  nationalBestBidMarketCenter : Alpha 1
  nationalBestBidPrice : BitVec 64
  nationalBestBidSize : BitVec 64
  nationalBestAskMarketCenter : Alpha 1
  nationalBestAskPrice : BitVec 64
  nationalBestAskSize : BitVec 64
  specialCondition : SpecialCondition
  marketCenterCloseRecap : Bounded 2 MarketCenterCloseRecap
  deriving DecidableEq, Repr

namespace SessionCloseRecapMessage

def encode (message : SessionCloseRecapMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo
    ++ (Alpha.encode message.symbolLong
    ++ (Alpha.encode message.nationalBestBidMarketCenter
    ++ (encodeUInt 8 message.nationalBestBidPrice
    ++ (encodeUInt 8 message.nationalBestBidSize
    ++ (Alpha.encode message.nationalBestAskMarketCenter
    ++ (encodeUInt 8 message.nationalBestAskPrice
    ++ (encodeUInt 8 message.nationalBestAskSize
    ++ (SpecialCondition.encode message.specialCondition
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.marketCenterCloseRecap.val.length)
    ++ (encodeMany MarketCenterCloseRecap.encode message.marketCenterCloseRecap.val))))))))))

def decode (bytes : List UInt8) : Option (SessionCloseRecapMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  let (symbolLong, bytes) ← Alpha.decode 11 bytes
  let (nationalBestBidMarketCenter, bytes) ← Alpha.decode 1 bytes
  let (nationalBestBidPrice, bytes) ← decodeUInt 8 bytes
  let (nationalBestBidSize, bytes) ← decodeUInt 8 bytes
  let (nationalBestAskMarketCenter, bytes) ← Alpha.decode 1 bytes
  let (nationalBestAskPrice, bytes) ← decodeUInt 8 bytes
  let (nationalBestAskSize, bytes) ← decodeUInt 8 bytes
  let (specialCondition, bytes) ← SpecialCondition.decode bytes
  let (numberOfMarketCenterAttachments, bytes) ← decodeUInt 2 bytes
  let (marketCenterCloseRecap_, bytes) ← decodeMany MarketCenterCloseRecap.decode numberOfMarketCenterAttachments.toNat bytes
  if fits_marketCenterCloseRecap : marketCenterCloseRecap_.length < 256 ^ 2 then
    pure ({ messageInfo, symbolLong, nationalBestBidMarketCenter, nationalBestBidPrice, nationalBestBidSize, nationalBestAskMarketCenter, nationalBestAskPrice, nationalBestAskSize, specialCondition, marketCenterCloseRecap := ⟨marketCenterCloseRecap_, fits_marketCenterCloseRecap⟩ }, bytes)
  else none

theorem encode_length_pos (message : SessionCloseRecapMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [MessageInfo.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SessionCloseRecapMessage) : (encode message).length ≤ 2162729 := by
  have bound_marketCenterCloseRecap := message.marketCenterCloseRecap.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, MessageInfo.encode_length, Alpha.encode_length, encodeUInt_length, SpecialCondition.encode_length, encodeMany_length_const MarketCenterCloseRecap.encode 33 MarketCenterCloseRecap.encode_length]
  omega

@[simp] theorem decode_encode (message : SessionCloseRecapMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MessageInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, SpecialCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 MarketCenterCloseRecap.encode MarketCenterCloseRecap.decode MarketCenterCloseRecap.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketCenterCloseRecap.length_lt]
  rfl

end SessionCloseRecapMessage

/-- Any Administrative Message Payload, selected by Administrative Message Type -/
inductive AdministrativeMessagePayload where
  | generalAdministrativeMessage (message : GeneralAdministrativeMessage) -- 'A' 0x41
  | crossSroTradingActionMessage (message : CrossSroTradingActionMessage) -- 'H' 0x48
  | marketCenterTradingActionMessage (message : MarketCenterTradingActionMessage) -- 'K' 0x4B
  | issueSymbolDirectoryMessage (message : IssueSymbolDirectoryMessage) -- 'B' 0x42
  | regulationShoShortSalePriceTestRestrictedIndicatorMessage (message : RegulationShoShortSalePriceTestRestrictedIndicatorMessage) -- 'V' 0x56
  | limitUpLimitDownPriceBandMessage (message : LimitUpLimitDownPriceBandMessage) -- 'P' 0x50
  | marketWideCircuitBreakerDeclineLevelMessage (message : MarketWideCircuitBreakerDeclineLevelMessage) -- 'C' 0x43
  | marketWideCircuitBreakerStatusMessage (message : MarketWideCircuitBreakerStatusMessage) -- 'D' 0x44
  | auctionCollarMessage (message : AuctionCollarMessage) -- 'E' 0x45
  | sessionCloseRecapMessage (message : SessionCloseRecapMessage) -- 'R' 0x52
  deriving DecidableEq, Repr

namespace AdministrativeMessagePayload

/-- The Administrative Message Type each message is sent under -/
def tag : AdministrativeMessagePayload → BitVec 8
  | .generalAdministrativeMessage _ => 65
  | .crossSroTradingActionMessage _ => 72
  | .marketCenterTradingActionMessage _ => 75
  | .issueSymbolDirectoryMessage _ => 66
  | .regulationShoShortSalePriceTestRestrictedIndicatorMessage _ => 86
  | .limitUpLimitDownPriceBandMessage _ => 80
  | .marketWideCircuitBreakerDeclineLevelMessage _ => 67
  | .marketWideCircuitBreakerStatusMessage _ => 68
  | .auctionCollarMessage _ => 69
  | .sessionCloseRecapMessage _ => 82

def encode : AdministrativeMessagePayload → List UInt8
  | .generalAdministrativeMessage message => GeneralAdministrativeMessage.encode message
  | .crossSroTradingActionMessage message => CrossSroTradingActionMessage.encode message
  | .marketCenterTradingActionMessage message => MarketCenterTradingActionMessage.encode message
  | .issueSymbolDirectoryMessage message => IssueSymbolDirectoryMessage.encode message
  | .regulationShoShortSalePriceTestRestrictedIndicatorMessage message => RegulationShoShortSalePriceTestRestrictedIndicatorMessage.encode message
  | .limitUpLimitDownPriceBandMessage message => LimitUpLimitDownPriceBandMessage.encode message
  | .marketWideCircuitBreakerDeclineLevelMessage message => MarketWideCircuitBreakerDeclineLevelMessage.encode message
  | .marketWideCircuitBreakerStatusMessage message => MarketWideCircuitBreakerStatusMessage.encode message
  | .auctionCollarMessage message => AuctionCollarMessage.encode message
  | .sessionCloseRecapMessage message => SessionCloseRecapMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AdministrativeMessagePayload) : (encode message).length ≤ 2162729 := by
  cases message with
  | generalAdministrativeMessage inner =>
    have bound_inner := GeneralAdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega
  | crossSroTradingActionMessage inner =>
    simp only [encode, CrossSroTradingActionMessage.encode_length]
    omega
  | marketCenterTradingActionMessage inner =>
    simp only [encode, MarketCenterTradingActionMessage.encode_length]
    omega
  | issueSymbolDirectoryMessage inner =>
    simp only [encode, IssueSymbolDirectoryMessage.encode_length]
    omega
  | regulationShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [encode, RegulationShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | limitUpLimitDownPriceBandMessage inner =>
    simp only [encode, LimitUpLimitDownPriceBandMessage.encode_length]
    omega
  | marketWideCircuitBreakerDeclineLevelMessage inner =>
    simp only [encode, MarketWideCircuitBreakerDeclineLevelMessage.encode_length]
    omega
  | marketWideCircuitBreakerStatusMessage inner =>
    simp only [encode, MarketWideCircuitBreakerStatusMessage.encode_length]
    omega
  | auctionCollarMessage inner =>
    simp only [encode, AuctionCollarMessage.encode_length]
    omega
  | sessionCloseRecapMessage inner =>
    have bound_inner := SessionCloseRecapMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AdministrativeMessagePayload × List UInt8) :=
  if tag = 65 then (GeneralAdministrativeMessage.decode bytes).map fun (message, rest) => (.generalAdministrativeMessage message, rest)
  else if tag = 72 then (CrossSroTradingActionMessage.decode bytes).map fun (message, rest) => (.crossSroTradingActionMessage message, rest)
  else if tag = 75 then (MarketCenterTradingActionMessage.decode bytes).map fun (message, rest) => (.marketCenterTradingActionMessage message, rest)
  else if tag = 66 then (IssueSymbolDirectoryMessage.decode bytes).map fun (message, rest) => (.issueSymbolDirectoryMessage message, rest)
  else if tag = 86 then (RegulationShoShortSalePriceTestRestrictedIndicatorMessage.decode bytes).map fun (message, rest) => (.regulationShoShortSalePriceTestRestrictedIndicatorMessage message, rest)
  else if tag = 80 then (LimitUpLimitDownPriceBandMessage.decode bytes).map fun (message, rest) => (.limitUpLimitDownPriceBandMessage message, rest)
  else if tag = 67 then (MarketWideCircuitBreakerDeclineLevelMessage.decode bytes).map fun (message, rest) => (.marketWideCircuitBreakerDeclineLevelMessage message, rest)
  else if tag = 68 then (MarketWideCircuitBreakerStatusMessage.decode bytes).map fun (message, rest) => (.marketWideCircuitBreakerStatusMessage message, rest)
  else if tag = 69 then (AuctionCollarMessage.decode bytes).map fun (message, rest) => (.auctionCollarMessage message, rest)
  else if tag = 82 then (SessionCloseRecapMessage.decode bytes).map fun (message, rest) => (.sessionCloseRecapMessage message, rest)
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
theorem encode_length_le (message : AdministrativeMessage) : (encode message).length ≤ 2162730 := by
  unfold encode
  cases message.administrativeMessagePayload with
  | generalAdministrativeMessage inner =>
    have bound_inner := GeneralAdministrativeMessage.encode_length_le inner
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | crossSroTradingActionMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, CrossSroTradingActionMessage.encode_length]
    omega
  | marketCenterTradingActionMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, MarketCenterTradingActionMessage.encode_length]
    omega
  | issueSymbolDirectoryMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, IssueSymbolDirectoryMessage.encode_length]
    omega
  | regulationShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, RegulationShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | limitUpLimitDownPriceBandMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, LimitUpLimitDownPriceBandMessage.encode_length]
    omega
  | marketWideCircuitBreakerDeclineLevelMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, MarketWideCircuitBreakerDeclineLevelMessage.encode_length]
    omega
  | marketWideCircuitBreakerStatusMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, MarketWideCircuitBreakerStatusMessage.encode_length]
    omega
  | auctionCollarMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, AuctionCollarMessage.encode_length]
    omega
  | sessionCloseRecapMessage inner =>
    have bound_inner := SessionCloseRecapMessage.encode_length_le inner
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : AdministrativeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [AdministrativeMessagePayload.decode_encode, some_bind]
  rfl

end AdministrativeMessage

/-- Start Of Day Message: 26 bytes -/
structure StartOfDayMessage where
  messageInfo : MessageInfo
  deriving DecidableEq, Repr

namespace StartOfDayMessage

def encode (message : StartOfDayMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo

def decode (bytes : List UInt8) : Option (StartOfDayMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  pure ({ messageInfo }, bytes)

@[simp] theorem encode_length (message : StartOfDayMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [MessageInfo.encode_length]

theorem encode_length_pos (message : StartOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MessageInfo.decode_encode, some_bind]
  rfl

end StartOfDayMessage

/-- End Of Day Message: 26 bytes -/
structure EndOfDayMessage where
  messageInfo : MessageInfo
  deriving DecidableEq, Repr

namespace EndOfDayMessage

def encode (message : EndOfDayMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo

def decode (bytes : List UInt8) : Option (EndOfDayMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  pure ({ messageInfo }, bytes)

@[simp] theorem encode_length (message : EndOfDayMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [MessageInfo.encode_length]

theorem encode_length_pos (message : EndOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MessageInfo.decode_encode, some_bind]
  rfl

end EndOfDayMessage

/-- Market Session Open Message: 26 bytes -/
structure MarketSessionOpenMessage where
  messageInfo : MessageInfo
  deriving DecidableEq, Repr

namespace MarketSessionOpenMessage

def encode (message : MarketSessionOpenMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo

def decode (bytes : List UInt8) : Option (MarketSessionOpenMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  pure ({ messageInfo }, bytes)

@[simp] theorem encode_length (message : MarketSessionOpenMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [MessageInfo.encode_length]

theorem encode_length_pos (message : MarketSessionOpenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketSessionOpenMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MessageInfo.decode_encode, some_bind]
  rfl

end MarketSessionOpenMessage

/-- Market Session Close Message: 26 bytes -/
structure MarketSessionCloseMessage where
  messageInfo : MessageInfo
  deriving DecidableEq, Repr

namespace MarketSessionCloseMessage

def encode (message : MarketSessionCloseMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo

def decode (bytes : List UInt8) : Option (MarketSessionCloseMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  pure ({ messageInfo }, bytes)

@[simp] theorem encode_length (message : MarketSessionCloseMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [MessageInfo.encode_length]

theorem encode_length_pos (message : MarketSessionCloseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketSessionCloseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MessageInfo.decode_encode, some_bind]
  rfl

end MarketSessionCloseMessage

/-- End Of Transmissions Message: 26 bytes -/
structure EndOfTransmissionsMessage where
  messageInfo : MessageInfo
  deriving DecidableEq, Repr

namespace EndOfTransmissionsMessage

def encode (message : EndOfTransmissionsMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo

def decode (bytes : List UInt8) : Option (EndOfTransmissionsMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  pure ({ messageInfo }, bytes)

@[simp] theorem encode_length (message : EndOfTransmissionsMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [MessageInfo.encode_length]

theorem encode_length_pos (message : EndOfTransmissionsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTransmissionsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MessageInfo.decode_encode, some_bind]
  rfl

end EndOfTransmissionsMessage

/-- Quote Wipe Out Message: 26 bytes -/
structure QuoteWipeOutMessage where
  messageInfo : MessageInfo
  deriving DecidableEq, Repr

namespace QuoteWipeOutMessage

def encode (message : QuoteWipeOutMessage) : List UInt8 :=
  MessageInfo.encode message.messageInfo

def decode (bytes : List UInt8) : Option (QuoteWipeOutMessage × List UInt8) := do
  let (messageInfo, bytes) ← MessageInfo.decode bytes
  pure ({ messageInfo }, bytes)

@[simp] theorem encode_length (message : QuoteWipeOutMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [MessageInfo.encode_length]

theorem encode_length_pos (message : QuoteWipeOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteWipeOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [MessageInfo.decode_encode, some_bind]
  rfl

end QuoteWipeOutMessage

/-- Any Control Message Payload, selected by Control Message Type -/
inductive ControlMessagePayload where
  | startOfDayMessage (message : StartOfDayMessage) -- 'I' 0x49
  | endOfDayMessage (message : EndOfDayMessage) -- 'J' 0x4A
  | marketSessionOpenMessage (message : MarketSessionOpenMessage) -- 'O' 0x4F
  | marketSessionCloseMessage (message : MarketSessionCloseMessage) -- 'C' 0x43
  | endOfTransmissionsMessage (message : EndOfTransmissionsMessage) -- 'Z' 0x5A
  | quoteWipeOutMessage (message : QuoteWipeOutMessage) -- 'P' 0x50
  deriving DecidableEq, Repr

namespace ControlMessagePayload

/-- The Control Message Type each message is sent under -/
def tag : ControlMessagePayload → BitVec 8
  | .startOfDayMessage _ => 73
  | .endOfDayMessage _ => 74
  | .marketSessionOpenMessage _ => 79
  | .marketSessionCloseMessage _ => 67
  | .endOfTransmissionsMessage _ => 90
  | .quoteWipeOutMessage _ => 80

def encode : ControlMessagePayload → List UInt8
  | .startOfDayMessage message => StartOfDayMessage.encode message
  | .endOfDayMessage message => EndOfDayMessage.encode message
  | .marketSessionOpenMessage message => MarketSessionOpenMessage.encode message
  | .marketSessionCloseMessage message => MarketSessionCloseMessage.encode message
  | .endOfTransmissionsMessage message => EndOfTransmissionsMessage.encode message
  | .quoteWipeOutMessage message => QuoteWipeOutMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ControlMessagePayload) : (encode message).length ≤ 26 := by
  cases message with
  | startOfDayMessage inner =>
    simp only [encode, StartOfDayMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [encode, EndOfDayMessage.encode_length]
    omega
  | marketSessionOpenMessage inner =>
    simp only [encode, MarketSessionOpenMessage.encode_length]
    omega
  | marketSessionCloseMessage inner =>
    simp only [encode, MarketSessionCloseMessage.encode_length]
    omega
  | endOfTransmissionsMessage inner =>
    simp only [encode, EndOfTransmissionsMessage.encode_length]
    omega
  | quoteWipeOutMessage inner =>
    simp only [encode, QuoteWipeOutMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ControlMessagePayload × List UInt8) :=
  if tag = 73 then (StartOfDayMessage.decode bytes).map fun (message, rest) => (.startOfDayMessage message, rest)
  else if tag = 74 then (EndOfDayMessage.decode bytes).map fun (message, rest) => (.endOfDayMessage message, rest)
  else if tag = 79 then (MarketSessionOpenMessage.decode bytes).map fun (message, rest) => (.marketSessionOpenMessage message, rest)
  else if tag = 67 then (MarketSessionCloseMessage.decode bytes).map fun (message, rest) => (.marketSessionCloseMessage message, rest)
  else if tag = 90 then (EndOfTransmissionsMessage.decode bytes).map fun (message, rest) => (.endOfTransmissionsMessage message, rest)
  else if tag = 80 then (QuoteWipeOutMessage.decode bytes).map fun (message, rest) => (.quoteWipeOutMessage message, rest)
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
theorem encode_length_le (message : ControlMessage) : (encode message).length ≤ 27 := by
  unfold encode
  cases message.controlMessagePayload with
  | startOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, StartOfDayMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, EndOfDayMessage.encode_length]
    omega
  | marketSessionOpenMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, MarketSessionOpenMessage.encode_length]
    omega
  | marketSessionCloseMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, MarketSessionCloseMessage.encode_length]
    omega
  | endOfTransmissionsMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, EndOfTransmissionsMessage.encode_length]
    omega
  | quoteWipeOutMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, QuoteWipeOutMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ControlMessagePayload.decode_encode, some_bind]
  rfl

end ControlMessage

/-- Any Payload, selected by Message Category -/
inductive Payload where
  | quoteMessage (message : QuoteMessage) -- 'Q' 0x51
  | administrativeMessage (message : AdministrativeMessage) -- 'A' 0x41
  | controlMessage (message : ControlMessage) -- 'C' 0x43
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Category each message is sent under -/
def tag : Payload → BitVec 8
  | .quoteMessage _ => 81
  | .administrativeMessage _ => 65
  | .controlMessage _ => 67

def encode : Payload → List UInt8
  | .quoteMessage message => QuoteMessage.encode message
  | .administrativeMessage message => AdministrativeMessage.encode message
  | .controlMessage message => ControlMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 2162730 := by
  cases message with
  | quoteMessage inner =>
    have bound_inner := QuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega
  | controlMessage inner =>
    have bound_inner := ControlMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 81 then (QuoteMessage.decode bytes).map fun (message, rest) => (.quoteMessage message, rest)
  else if tag = 65 then (AdministrativeMessage.decode bytes).map fun (message, rest) => (.administrativeMessage message, rest)
  else if tag = 67 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  version : BitVec 8
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 message.version
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (version, bytes) ← decodeUInt 1 bytes
  let (messageCategory, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageCategory bytes
  pure ({ version, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Size rule: Message Length counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : Message) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end Message

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequence : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 8 message.sequence
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequence, bytes) ← decodeUInt 8 bytes
  let (count, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode count.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequence, message := ⟨message_, fits_message⟩ }, bytes)
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

end Omi.NasdaqUqdfOutputUtpV15
