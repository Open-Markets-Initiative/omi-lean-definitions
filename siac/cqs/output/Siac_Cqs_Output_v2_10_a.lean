import Wire

/-!
# The Securities Industry Automation Corporation  v2.10.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: National Bbo Indicator chooses the National Best Bid Long Appendage or National Best Offer Long Appendage or National Best Bid And Offer Long Appendage or National Best Bid Short Appendage or National Best Offer Short Appendage or National Best Bid And Offer Short Appendage attached, or none: it is written from the choice, and a value it does not list is not decoded.

Note: Block Pad Byte pads to a 2 byte boundary: it is read as the bytes left to the end of the frame, fewer than 2, and the frame's length is trusted to keep the boundary.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.SiacCqsOutputCtaV210A

/-- Participant Id: one byte code -/
def ParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive ParticipantId where
  | nyseAmerican -- Nyse American
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nyseNational -- Nyse National
  | finraAdf -- Finra Adf
  | n24X -- N 24 X
  | miax -- Miax
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseTexas -- Nyse Texas
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | cqs -- Cqs
  | nasdaq -- Nasdaq
  | memx -- Memx
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqOmxPsx -- Nasdaq Omx Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | unlisted (byte : { byte : UInt8 // byte ∉ ParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ParticipantId

def toByte : ParticipantId → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqOmxBx => 0x42
  | .nyseNational => 0x43
  | .finraAdf => 0x44
  | .n24X => 0x47
  | .miax => 0x48
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseTexas => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .cqs => 0x53
  | .nasdaq => 0x54
  | .memx => 0x55
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqOmxPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ParticipantId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqOmxBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finraAdf
  else if byte = 0x47 then .n24X
  else if byte = 0x48 then .miax
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x53 then .cqs
  else if byte = 0x54 then .nasdaq
  else if byte = 0x55 then .memx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqOmxPsx
  else if byte = 0x59 then .cboeByx
  else .cboeBzx

def ofByte (byte : UInt8) : ParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ParticipantId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqOmxBx => decide
  | nyseNational => decide
  | finraAdf => decide
  | n24X => decide
  | miax => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseTexas => decide
  | nyse => decide
  | nyseArca => decide
  | cqs => decide
  | nasdaq => decide
  | memx => decide
  | iex => decide
  | cbsx => decide
  | nasdaqOmxPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ParticipantId

/-- Primary Listing Market Participant Id: one byte code -/
def PrimaryListingMarketParticipantId.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive PrimaryListingMarketParticipantId where
  | primaryListingMarketParticipantIdNotApplicable -- Primary Listing Market Participant Id Not Applicable
  | nyseAmerican -- Nyse American
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nyseNational -- Nyse National
  | finraAdf -- Finra Adf
  | n24X -- N 24 X
  | miaxPearl -- Miax Pearl
  | ise -- Ise
  | cboeEdga -- Cboe Edga
  | cboeEdgx -- Cboe Edgx
  | ltse -- Ltse
  | nyseTexas -- Nyse Texas
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | membersExchange -- Members Exchange
  | iex -- Iex
  | cbsx -- Cbsx
  | nasdaqOmxPsx -- Nasdaq Omx Psx
  | cboeByx -- Cboe Byx
  | cboeBzx -- Cboe Bzx
  | unlisted (byte : { byte : UInt8 // byte ∉ PrimaryListingMarketParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrimaryListingMarketParticipantId

def toByte : PrimaryListingMarketParticipantId → UInt8
  | .primaryListingMarketParticipantIdNotApplicable => 0x20
  | .nyseAmerican => 0x41
  | .nasdaqOmxBx => 0x42
  | .nyseNational => 0x43
  | .finraAdf => 0x44
  | .n24X => 0x47
  | .miaxPearl => 0x48
  | .ise => 0x49
  | .cboeEdga => 0x4A
  | .cboeEdgx => 0x4B
  | .ltse => 0x4C
  | .nyseTexas => 0x4D
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x54
  | .membersExchange => 0x55
  | .iex => 0x56
  | .cbsx => 0x57
  | .nasdaqOmxPsx => 0x58
  | .cboeByx => 0x59
  | .cboeBzx => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrimaryListingMarketParticipantId :=
  if byte = 0x20 then .primaryListingMarketParticipantIdNotApplicable
  else if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqOmxBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x44 then .finraAdf
  else if byte = 0x47 then .n24X
  else if byte = 0x48 then .miaxPearl
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .cboeEdga
  else if byte = 0x4B then .cboeEdgx
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x54 then .nasdaq
  else if byte = 0x55 then .membersExchange
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cbsx
  else if byte = 0x58 then .nasdaqOmxPsx
  else if byte = 0x59 then .cboeByx
  else .cboeBzx

def ofByte (byte : UInt8) : PrimaryListingMarketParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrimaryListingMarketParticipantId) : ofByte value.toByte = value := by
  cases value with
  | primaryListingMarketParticipantIdNotApplicable => decide
  | nyseAmerican => decide
  | nasdaqOmxBx => decide
  | nyseNational => decide
  | finraAdf => decide
  | n24X => decide
  | miaxPearl => decide
  | ise => decide
  | cboeEdga => decide
  | cboeEdgx => decide
  | ltse => decide
  | nyseTexas => decide
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | membersExchange => decide
  | iex => decide
  | cbsx => decide
  | nasdaqOmxPsx => decide
  | cboeByx => decide
  | cboeBzx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrimaryListingMarketParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrimaryListingMarketParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrimaryListingMarketParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrimaryListingMarketParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrimaryListingMarketParticipantId

/-- Luld Tier: one byte code -/
def LuldTier.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive LuldTier where
  | luldNotApplicable -- Luld Not Applicable
  | luldTier1Security -- Luld Tier 1 Security
  | luldTier2Security -- Luld Tier 2 Security
  | unlisted (byte : { byte : UInt8 // byte ∉ LuldTier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LuldTier

def toByte : LuldTier → UInt8
  | .luldNotApplicable => 0x30
  | .luldTier1Security => 0x31
  | .luldTier2Security => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LuldTier :=
  if byte = 0x30 then .luldNotApplicable
  else if byte = 0x31 then .luldTier1Security
  else .luldTier2Security

def ofByte (byte : UInt8) : LuldTier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LuldTier) : ofByte value.toByte = value := by
  cases value with
  | luldNotApplicable => decide
  | luldTier1Security => decide
  | luldTier2Security => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LuldTier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LuldTier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LuldTier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LuldTier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LuldTier

/-- Test: one byte code -/
def Test.codes : List UInt8 :=
  [0x30, 0x31]

inductive Test where
  | notATestSymbol -- Not A Test Symbol
  | testSymbol -- Test Symbol
  | unlisted (byte : { byte : UInt8 // byte ∉ Test.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Test

def toByte : Test → UInt8
  | .notATestSymbol => 0x30
  | .testSymbol => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Test :=
  if byte = 0x30 then .notATestSymbol
  else .testSymbol

def ofByte (byte : UInt8) : Test :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Test) : ofByte value.toByte = value := by
  cases value with
  | notATestSymbol => decide
  | testSymbol => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Test) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Test × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Test) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Test) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Test

/-- Ipo: one byte code -/
def Ipo.codes : List UInt8 :=
  [0x30, 0x31]

inductive Ipo where
  | notAnIpoSymbol -- Not An Ipo Symbol
  | ipoSymbol -- Ipo Symbol
  | unlisted (byte : { byte : UInt8 // byte ∉ Ipo.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Ipo

def toByte : Ipo → UInt8
  | .notAnIpoSymbol => 0x30
  | .ipoSymbol => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Ipo :=
  if byte = 0x30 then .notAnIpoSymbol
  else .ipoSymbol

def ofByte (byte : UInt8) : Ipo :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Ipo) : ofByte value.toByte = value := by
  cases value with
  | notAnIpoSymbol => decide
  | ipoSymbol => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Ipo) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Ipo × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Ipo) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Ipo) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Ipo

/-- Financial Status Indicator: one byte code -/
def FinancialStatusIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41]

inductive FinancialStatusIndicator where
  | financialStatusNotApplicable -- Financial Status Not Applicable
  | bankrupt -- Bankrupt
  | belowContinuingListingStandards -- Below Continuing Listing Standards
  | bankruptAndBelowContinuingListingStandards -- Bankrupt And Below Continuing Listing Standards
  | lateFiling -- Late Filing
  | bankruptAndLateFiling -- Bankrupt And Late Filing
  | belowContinuingListingStandardsAndLateFiling -- Below Continuing Listing Standards And Late Filing
  | bankruptBelowContinuingListingStandardsAndLateFiling -- Bankrupt Below Continuing Listing Standards And Late Filing
  | creationsSuspended -- Creations Suspended
  | redemptionsSuspended -- Redemptions Suspended
  | liquidation -- Liquidation
  | unlisted (byte : { byte : UInt8 // byte ∉ FinancialStatusIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinancialStatusIndicator

def toByte : FinancialStatusIndicator → UInt8
  | .financialStatusNotApplicable => 0x30
  | .bankrupt => 0x31
  | .belowContinuingListingStandards => 0x32
  | .bankruptAndBelowContinuingListingStandards => 0x33
  | .lateFiling => 0x34
  | .bankruptAndLateFiling => 0x35
  | .belowContinuingListingStandardsAndLateFiling => 0x36
  | .bankruptBelowContinuingListingStandardsAndLateFiling => 0x37
  | .creationsSuspended => 0x38
  | .redemptionsSuspended => 0x39
  | .liquidation => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinancialStatusIndicator :=
  if byte = 0x30 then .financialStatusNotApplicable
  else if byte = 0x31 then .bankrupt
  else if byte = 0x32 then .belowContinuingListingStandards
  else if byte = 0x33 then .bankruptAndBelowContinuingListingStandards
  else if byte = 0x34 then .lateFiling
  else if byte = 0x35 then .bankruptAndLateFiling
  else if byte = 0x36 then .belowContinuingListingStandardsAndLateFiling
  else if byte = 0x37 then .bankruptBelowContinuingListingStandardsAndLateFiling
  else if byte = 0x38 then .creationsSuspended
  else if byte = 0x39 then .redemptionsSuspended
  else .liquidation

def ofByte (byte : UInt8) : FinancialStatusIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinancialStatusIndicator) : ofByte value.toByte = value := by
  cases value with
  | financialStatusNotApplicable => decide
  | bankrupt => decide
  | belowContinuingListingStandards => decide
  | bankruptAndBelowContinuingListingStandards => decide
  | lateFiling => decide
  | bankruptAndLateFiling => decide
  | belowContinuingListingStandardsAndLateFiling => decide
  | bankruptBelowContinuingListingStandardsAndLateFiling => decide
  | creationsSuspended => decide
  | redemptionsSuspended => decide
  | liquidation => decide
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

/-- Short Sale Restriction Indicator: one byte code -/
def ShortSaleRestrictionIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x43, 0x44, 0x45]

inductive ShortSaleRestrictionIndicator where
  | shortSaleRestrictionNotInEffect -- Short Sale Restriction Not In Effect
  | shortSaleRestrictionActivated -- Short Sale Restriction Activated
  | shortSaleRestrictionContinued -- Short Sale Restriction Continued
  | shortSaleRestrictionDeactivated -- Short Sale Restriction Deactivated
  | shortSaleRestrictionInEffect -- Short Sale Restriction In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSaleRestrictionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSaleRestrictionIndicator

def toByte : ShortSaleRestrictionIndicator → UInt8
  | .shortSaleRestrictionNotInEffect => 0x20
  | .shortSaleRestrictionActivated => 0x41
  | .shortSaleRestrictionContinued => 0x43
  | .shortSaleRestrictionDeactivated => 0x44
  | .shortSaleRestrictionInEffect => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSaleRestrictionIndicator :=
  if byte = 0x20 then .shortSaleRestrictionNotInEffect
  else if byte = 0x41 then .shortSaleRestrictionActivated
  else if byte = 0x43 then .shortSaleRestrictionContinued
  else if byte = 0x44 then .shortSaleRestrictionDeactivated
  else .shortSaleRestrictionInEffect

def ofByte (byte : UInt8) : ShortSaleRestrictionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSaleRestrictionIndicator) : ofByte value.toByte = value := by
  cases value with
  | shortSaleRestrictionNotInEffect => decide
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

/-- Market Wide Circuit Breaker Level Indicator: one byte code -/
def MarketWideCircuitBreakerLevelIndicator.codes : List UInt8 :=
  [0x20, 0x31, 0x32, 0x33]

inductive MarketWideCircuitBreakerLevelIndicator where
  | mwcbNotApplicable -- Mwcb Not Applicable
  | level1Breached -- Level 1 Breached
  | level2Breached -- Level 2 Breached
  | level3Breached -- Level 3 Breached
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketWideCircuitBreakerLevelIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerLevelIndicator

def toByte : MarketWideCircuitBreakerLevelIndicator → UInt8
  | .mwcbNotApplicable => 0x20
  | .level1Breached => 0x31
  | .level2Breached => 0x32
  | .level3Breached => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketWideCircuitBreakerLevelIndicator :=
  if byte = 0x20 then .mwcbNotApplicable
  else if byte = 0x31 then .level1Breached
  else if byte = 0x32 then .level2Breached
  else .level3Breached

def ofByte (byte : UInt8) : MarketWideCircuitBreakerLevelIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketWideCircuitBreakerLevelIndicator) : ofByte value.toByte = value := by
  cases value with
  | mwcbNotApplicable => decide
  | level1Breached => decide
  | level2Breached => decide
  | level3Breached => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketWideCircuitBreakerLevelIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketWideCircuitBreakerLevelIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketWideCircuitBreakerLevelIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketWideCircuitBreakerLevelIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketWideCircuitBreakerLevelIndicator

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x45, 0x46, 0x48, 0x4C, 0x4E, 0x4F, 0x52, 0x55, 0x57, 0x34]

inductive QuoteCondition where
  | quoteConditionNotApplicable -- Quote Condition Not Applicable
  | slowQuoteOnOfferSide -- Slow Quote On Offer Side
  | slowQuoteOnBidSide -- Slow Quote On Bid Side
  | closing -- Closing
  | slowQuoteDueToLrpOrGapQuoteOnTheBidSide -- Slow Quote Due To Lrp Or Gap Quote On The Bid Side
  | slowQuoteDueToLrpOrGapQuoteOnTheOfferSide -- Slow Quote Due To Lrp Or Gap Quote On The Offer Side
  | slowQuoteOnTheBidAndOfferSides -- Slow Quote On The Bid And Offer Sides
  | closedMarketMaker -- Closed Market Maker
  | nonFirmQuote -- Non Firm Quote
  | openingQuote -- Opening Quote
  | regular -- Regular
  | slowQuoteDueToLrpOrGapQuoteOnBothSides -- Slow Quote Due To Lrp Or Gap Quote On Both Sides
  | slowQuoteDueToSetSlowListOnBothSides -- Slow Quote Due To Set Slow List On Both Sides
  | onDemandIntraDayAuction -- On Demand Intra Day Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .quoteConditionNotApplicable => 0x20
  | .slowQuoteOnOfferSide => 0x41
  | .slowQuoteOnBidSide => 0x42
  | .closing => 0x43
  | .slowQuoteDueToLrpOrGapQuoteOnTheBidSide => 0x45
  | .slowQuoteDueToLrpOrGapQuoteOnTheOfferSide => 0x46
  | .slowQuoteOnTheBidAndOfferSides => 0x48
  | .closedMarketMaker => 0x4C
  | .nonFirmQuote => 0x4E
  | .openingQuote => 0x4F
  | .regular => 0x52
  | .slowQuoteDueToLrpOrGapQuoteOnBothSides => 0x55
  | .slowQuoteDueToSetSlowListOnBothSides => 0x57
  | .onDemandIntraDayAuction => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x20 then .quoteConditionNotApplicable
  else if byte = 0x41 then .slowQuoteOnOfferSide
  else if byte = 0x42 then .slowQuoteOnBidSide
  else if byte = 0x43 then .closing
  else if byte = 0x45 then .slowQuoteDueToLrpOrGapQuoteOnTheBidSide
  else if byte = 0x46 then .slowQuoteDueToLrpOrGapQuoteOnTheOfferSide
  else if byte = 0x48 then .slowQuoteOnTheBidAndOfferSides
  else if byte = 0x4C then .closedMarketMaker
  else if byte = 0x4E then .nonFirmQuote
  else if byte = 0x4F then .openingQuote
  else if byte = 0x52 then .regular
  else if byte = 0x55 then .slowQuoteDueToLrpOrGapQuoteOnBothSides
  else if byte = 0x57 then .slowQuoteDueToSetSlowListOnBothSides
  else .onDemandIntraDayAuction

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | quoteConditionNotApplicable => decide
  | slowQuoteOnOfferSide => decide
  | slowQuoteOnBidSide => decide
  | closing => decide
  | slowQuoteDueToLrpOrGapQuoteOnTheBidSide => decide
  | slowQuoteDueToLrpOrGapQuoteOnTheOfferSide => decide
  | slowQuoteOnTheBidAndOfferSides => decide
  | closedMarketMaker => decide
  | nonFirmQuote => decide
  | openingQuote => decide
  | regular => decide
  | slowQuoteDueToLrpOrGapQuoteOnBothSides => decide
  | slowQuoteDueToSetSlowListOnBothSides => decide
  | onDemandIntraDayAuction => decide
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

/-- Security Status Indicator: one byte code -/
def SecurityStatusIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x43, 0x44, 0x45, 0x46, 0x47, 0x49, 0x4D, 0x4E, 0x4F, 0x50, 0x56, 0x54, 0x58, 0x59, 0x5A, 0x30, 0x31, 0x32, 0x33, 0x39]

inductive SecurityStatusIndicator where
  | securityStatusIndicatorNotApplicable -- Security Status Indicator Not Applicable
  | additionalInformationRequested -- Additional Information Requested
  | regulatoryConcern -- Regulatory Concern
  | newsReleased -- News Released
  | mergerEffective -- Merger Effective
  | etfComponentPricesNotAvailable -- Etf Component Prices Not Available
  | tradingRangeIndication -- Trading Range Indication
  | orderImbalance -- Order Imbalance
  | limitUpLimitDownTradingPause -- Limit Up Limit Down Trading Pause
  | corporateAction -- Corporate Action
  | newSecurityOffering -- New Security Offering
  | newsPending -- News Pending
  | intradayIndicativeValueNotAvailable -- Intraday Indicative Value Not Available
  | resume -- Resume
  | operational -- Operational
  | supPennyTrading -- Sup Penny Trading
  | reserved -- Reserved
  | limitUpLimitDownPriceBand -- Limit Up Limit Down Price Band
  | marketWideCircuitBreakerLevel1Breached -- Market Wide Circuit Breaker Level 1 Breached
  | marketWideCircuitBreakerLevel2Breached -- Market Wide Circuit Breaker Level 2 Breached
  | marketWideCircuitBreakerLevel3Breached -- Market Wide Circuit Breaker Level 3 Breached
  | republishedLimitUpLimitDownPriceBand -- Republished Limit Up Limit Down Price Band
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatusIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatusIndicator

def toByte : SecurityStatusIndicator → UInt8
  | .securityStatusIndicatorNotApplicable => 0x20
  | .additionalInformationRequested => 0x41
  | .regulatoryConcern => 0x43
  | .newsReleased => 0x44
  | .mergerEffective => 0x45
  | .etfComponentPricesNotAvailable => 0x46
  | .tradingRangeIndication => 0x47
  | .orderImbalance => 0x49
  | .limitUpLimitDownTradingPause => 0x4D
  | .corporateAction => 0x4E
  | .newSecurityOffering => 0x4F
  | .newsPending => 0x50
  | .intradayIndicativeValueNotAvailable => 0x56
  | .resume => 0x54
  | .operational => 0x58
  | .supPennyTrading => 0x59
  | .reserved => 0x5A
  | .limitUpLimitDownPriceBand => 0x30
  | .marketWideCircuitBreakerLevel1Breached => 0x31
  | .marketWideCircuitBreakerLevel2Breached => 0x32
  | .marketWideCircuitBreakerLevel3Breached => 0x33
  | .republishedLimitUpLimitDownPriceBand => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatusIndicator :=
  if byte = 0x20 then .securityStatusIndicatorNotApplicable
  else if byte = 0x41 then .additionalInformationRequested
  else if byte = 0x43 then .regulatoryConcern
  else if byte = 0x44 then .newsReleased
  else if byte = 0x45 then .mergerEffective
  else if byte = 0x46 then .etfComponentPricesNotAvailable
  else if byte = 0x47 then .tradingRangeIndication
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x4D then .limitUpLimitDownTradingPause
  else if byte = 0x4E then .corporateAction
  else if byte = 0x4F then .newSecurityOffering
  else if byte = 0x50 then .newsPending
  else if byte = 0x56 then .intradayIndicativeValueNotAvailable
  else if byte = 0x54 then .resume
  else if byte = 0x58 then .operational
  else if byte = 0x59 then .supPennyTrading
  else if byte = 0x5A then .reserved
  else if byte = 0x30 then .limitUpLimitDownPriceBand
  else if byte = 0x31 then .marketWideCircuitBreakerLevel1Breached
  else if byte = 0x32 then .marketWideCircuitBreakerLevel2Breached
  else if byte = 0x33 then .marketWideCircuitBreakerLevel3Breached
  else .republishedLimitUpLimitDownPriceBand

def ofByte (byte : UInt8) : SecurityStatusIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatusIndicator) : ofByte value.toByte = value := by
  cases value with
  | securityStatusIndicatorNotApplicable => decide
  | additionalInformationRequested => decide
  | regulatoryConcern => decide
  | newsReleased => decide
  | mergerEffective => decide
  | etfComponentPricesNotAvailable => decide
  | tradingRangeIndication => decide
  | orderImbalance => decide
  | limitUpLimitDownTradingPause => decide
  | corporateAction => decide
  | newSecurityOffering => decide
  | newsPending => decide
  | intradayIndicativeValueNotAvailable => decide
  | resume => decide
  | operational => decide
  | supPennyTrading => decide
  | reserved => decide
  | limitUpLimitDownPriceBand => decide
  | marketWideCircuitBreakerLevel1Breached => decide
  | marketWideCircuitBreakerLevel2Breached => decide
  | marketWideCircuitBreakerLevel3Breached => decide
  | republishedLimitUpLimitDownPriceBand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityStatusIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityStatusIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityStatusIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityStatusIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityStatusIndicator

/-- Retail Interest Indicator: one byte code -/
def RetailInterestIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43]

inductive RetailInterestIndicator where
  | retailInterestIndicatorNotApplicable -- Retail Interest Indicator Not Applicable
  | retailInterestOnBidQuote -- Retail Interest On Bid Quote
  | retailInterestOnOfferQuote -- Retail Interest On Offer Quote
  | retailInterestOnBothTheBidAndOfferQuotes -- Retail Interest On Both The Bid And Offer Quotes
  | unlisted (byte : { byte : UInt8 // byte ∉ RetailInterestIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetailInterestIndicator

def toByte : RetailInterestIndicator → UInt8
  | .retailInterestIndicatorNotApplicable => 0x20
  | .retailInterestOnBidQuote => 0x41
  | .retailInterestOnOfferQuote => 0x42
  | .retailInterestOnBothTheBidAndOfferQuotes => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RetailInterestIndicator :=
  if byte = 0x20 then .retailInterestIndicatorNotApplicable
  else if byte = 0x41 then .retailInterestOnBidQuote
  else if byte = 0x42 then .retailInterestOnOfferQuote
  else .retailInterestOnBothTheBidAndOfferQuotes

def ofByte (byte : UInt8) : RetailInterestIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetailInterestIndicator) : ofByte value.toByte = value := by
  cases value with
  | retailInterestIndicatorNotApplicable => decide
  | retailInterestOnBidQuote => decide
  | retailInterestOnOfferQuote => decide
  | retailInterestOnBothTheBidAndOfferQuotes => decide
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

/-- Settlement Condition: one byte code -/
def SettlementCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42]

inductive SettlementCondition where
  | regularWaySettlement -- Regular Way Settlement
  | cashSettlement -- Cash Settlement
  | nextDaySettlement -- Next Day Settlement
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementCondition

def toByte : SettlementCondition → UInt8
  | .regularWaySettlement => 0x20
  | .cashSettlement => 0x41
  | .nextDaySettlement => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementCondition :=
  if byte = 0x20 then .regularWaySettlement
  else if byte = 0x41 then .cashSettlement
  else .nextDaySettlement

def ofByte (byte : UInt8) : SettlementCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementCondition) : ofByte value.toByte = value := by
  cases value with
  | regularWaySettlement => decide
  | cashSettlement => decide
  | nextDaySettlement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlementCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementCondition

/-- Market Condition: one byte code -/
def MarketCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42]

inductive MarketCondition where
  | normalAuctionMarket -- Normal Auction Market
  | crossedMarket -- Crossed Market
  | lockedMarket -- Locked Market
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCondition

def toByte : MarketCondition → UInt8
  | .normalAuctionMarket => 0x20
  | .crossedMarket => 0x41
  | .lockedMarket => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCondition :=
  if byte = 0x20 then .normalAuctionMarket
  else if byte = 0x41 then .crossedMarket
  else .lockedMarket

def ofByte (byte : UInt8) : MarketCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCondition) : ofByte value.toByte = value := by
  cases value with
  | normalAuctionMarket => decide
  | crossedMarket => decide
  | lockedMarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCondition

/-- Finra Bbo Indicator: one byte code -/
def FinraBboIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42]

inductive FinraBboIndicator where
  | finraBboIndicatorNotApplicable -- Finra Bbo Indicator Not Applicable
  | noFinraBboChange -- No Finra Bbo Change
  | noFinraBboExists -- No Finra Bbo Exists
  | unlisted (byte : { byte : UInt8 // byte ∉ FinraBboIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinraBboIndicator

def toByte : FinraBboIndicator → UInt8
  | .finraBboIndicatorNotApplicable => 0x20
  | .noFinraBboChange => 0x41
  | .noFinraBboExists => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinraBboIndicator :=
  if byte = 0x20 then .finraBboIndicatorNotApplicable
  else if byte = 0x41 then .noFinraBboChange
  else .noFinraBboExists

def ofByte (byte : UInt8) : FinraBboIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinraBboIndicator) : ofByte value.toByte = value := by
  cases value with
  | finraBboIndicatorNotApplicable => decide
  | noFinraBboChange => decide
  | noFinraBboExists => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FinraBboIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinraBboIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FinraBboIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FinraBboIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FinraBboIndicator

/-- Sip Generated Message Identifier: one byte code -/
def SipGeneratedMessageIdentifier.codes : List UInt8 :=
  [0x20, 0x53]

inductive SipGeneratedMessageIdentifier where
  | sipGeneratedMessageNotApplicable -- Sip Generated Message Not Applicable
  | consolidatedQuotationSystem -- Consolidated Quotation System
  | unlisted (byte : { byte : UInt8 // byte ∉ SipGeneratedMessageIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SipGeneratedMessageIdentifier

def toByte : SipGeneratedMessageIdentifier → UInt8
  | .sipGeneratedMessageNotApplicable => 0x20
  | .consolidatedQuotationSystem => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SipGeneratedMessageIdentifier :=
  if byte = 0x20 then .sipGeneratedMessageNotApplicable
  else .consolidatedQuotationSystem

def ofByte (byte : UInt8) : SipGeneratedMessageIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SipGeneratedMessageIdentifier) : ofByte value.toByte = value := by
  cases value with
  | sipGeneratedMessageNotApplicable => decide
  | consolidatedQuotationSystem => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SipGeneratedMessageIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SipGeneratedMessageIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SipGeneratedMessageIdentifier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SipGeneratedMessageIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SipGeneratedMessageIdentifier

/-- Limit Up Limit Down Luld Indicator: one byte code -/
def LimitUpLimitDownLuldIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42]

inductive LimitUpLimitDownLuldIndicator where
  | limitUpLimitDownNotApplicable -- Limit Up Limit Down Not Applicable
  | bidPriceAboveUpperLimitPriceBand -- Bid Price Above Upper Limit Price Band
  | offerPriceBelowLowerLimitPriceBand -- Offer Price Below Lower Limit Price Band
  | unlisted (byte : { byte : UInt8 // byte ∉ LimitUpLimitDownLuldIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LimitUpLimitDownLuldIndicator

def toByte : LimitUpLimitDownLuldIndicator → UInt8
  | .limitUpLimitDownNotApplicable => 0x20
  | .bidPriceAboveUpperLimitPriceBand => 0x41
  | .offerPriceBelowLowerLimitPriceBand => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LimitUpLimitDownLuldIndicator :=
  if byte = 0x20 then .limitUpLimitDownNotApplicable
  else if byte = 0x41 then .bidPriceAboveUpperLimitPriceBand
  else .offerPriceBelowLowerLimitPriceBand

def ofByte (byte : UInt8) : LimitUpLimitDownLuldIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LimitUpLimitDownLuldIndicator) : ofByte value.toByte = value := by
  cases value with
  | limitUpLimitDownNotApplicable => decide
  | bidPriceAboveUpperLimitPriceBand => decide
  | offerPriceBelowLowerLimitPriceBand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LimitUpLimitDownLuldIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LimitUpLimitDownLuldIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LimitUpLimitDownLuldIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LimitUpLimitDownLuldIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LimitUpLimitDownLuldIndicator

/-- National Bbo Luld Indicator: one byte code -/
def NationalBboLuldIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49]

inductive NationalBboLuldIndicator where
  | limitUpLimitDownNotApplicable -- Limit Up Limit Down Not Applicable
  | nationalBestBidAndorNationalBestOfferAreExecutable -- National Best Bid Andor National Best Offer Are Executable
  | nationalBestBidBelowLowerLimitPriceBand -- National Best Bid Below Lower Limit Price Band
  | nationalBestOfferAboveUpperLimitPriceBand -- National Best Offer Above Upper Limit Price Band
  | nationalBestBidBelowLowerAndNationalBestOfferAboveUpperLimitPriceBand -- National Best Bid Below Lower And National Best Offer Above Upper Limit Price Band
  | nationalBestBidEqualsUpperLimitPriceBand -- National Best Bid Equals Upper Limit Price Band
  | nationalBestOfferEqualsLowerLimitPriceBand -- National Best Offer Equals Lower Limit Price Band
  | nationalBestBidInLimitStateAndNationalBestOfferNonExecutable -- National Best Bid In Limit State And National Best Offer Non Executable
  | nationalBestBidNonExecutableAndNationalBestOfferInLimitState -- National Best Bid Non Executable And National Best Offer In Limit State
  | nationalBestBidEqualsUpperAndNationalBestOfferEqualsLowerLimitPriceBand -- National Best Bid Equals Upper And National Best Offer Equals Lower Limit Price Band
  | unlisted (byte : { byte : UInt8 // byte ∉ NationalBboLuldIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NationalBboLuldIndicator

def toByte : NationalBboLuldIndicator → UInt8
  | .limitUpLimitDownNotApplicable => 0x20
  | .nationalBestBidAndorNationalBestOfferAreExecutable => 0x41
  | .nationalBestBidBelowLowerLimitPriceBand => 0x42
  | .nationalBestOfferAboveUpperLimitPriceBand => 0x43
  | .nationalBestBidBelowLowerAndNationalBestOfferAboveUpperLimitPriceBand => 0x44
  | .nationalBestBidEqualsUpperLimitPriceBand => 0x45
  | .nationalBestOfferEqualsLowerLimitPriceBand => 0x46
  | .nationalBestBidInLimitStateAndNationalBestOfferNonExecutable => 0x47
  | .nationalBestBidNonExecutableAndNationalBestOfferInLimitState => 0x48
  | .nationalBestBidEqualsUpperAndNationalBestOfferEqualsLowerLimitPriceBand => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NationalBboLuldIndicator :=
  if byte = 0x20 then .limitUpLimitDownNotApplicable
  else if byte = 0x41 then .nationalBestBidAndorNationalBestOfferAreExecutable
  else if byte = 0x42 then .nationalBestBidBelowLowerLimitPriceBand
  else if byte = 0x43 then .nationalBestOfferAboveUpperLimitPriceBand
  else if byte = 0x44 then .nationalBestBidBelowLowerAndNationalBestOfferAboveUpperLimitPriceBand
  else if byte = 0x45 then .nationalBestBidEqualsUpperLimitPriceBand
  else if byte = 0x46 then .nationalBestOfferEqualsLowerLimitPriceBand
  else if byte = 0x47 then .nationalBestBidInLimitStateAndNationalBestOfferNonExecutable
  else if byte = 0x48 then .nationalBestBidNonExecutableAndNationalBestOfferInLimitState
  else .nationalBestBidEqualsUpperAndNationalBestOfferEqualsLowerLimitPriceBand

def ofByte (byte : UInt8) : NationalBboLuldIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NationalBboLuldIndicator) : ofByte value.toByte = value := by
  cases value with
  | limitUpLimitDownNotApplicable => decide
  | nationalBestBidAndorNationalBestOfferAreExecutable => decide
  | nationalBestBidBelowLowerLimitPriceBand => decide
  | nationalBestOfferAboveUpperLimitPriceBand => decide
  | nationalBestBidBelowLowerAndNationalBestOfferAboveUpperLimitPriceBand => decide
  | nationalBestBidEqualsUpperLimitPriceBand => decide
  | nationalBestOfferEqualsLowerLimitPriceBand => decide
  | nationalBestBidInLimitStateAndNationalBestOfferNonExecutable => decide
  | nationalBestBidNonExecutableAndNationalBestOfferInLimitState => decide
  | nationalBestBidEqualsUpperAndNationalBestOfferEqualsLowerLimitPriceBand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NationalBboLuldIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NationalBboLuldIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NationalBboLuldIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : NationalBboLuldIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NationalBboLuldIndicator

/-- Finra Bbo Luld Indicator: one byte code -/
def FinraBboLuldIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44]

inductive FinraBboLuldIndicator where
  | limitUpLimitDownNotApplicable -- Limit Up Limit Down Not Applicable
  | finraBestBidAndFinraBestOfferAreExecutable -- Finra Best Bid And Finra Best Offer Are Executable
  | finraBestBidOutsidePriceBand -- Finra Best Bid Outside Price Band
  | finraBestOfferOutsidePriceBand -- Finra Best Offer Outside Price Band
  | finraBestBidAndFinraBestOfferOutsidePriceBand -- Finra Best Bid And Finra Best Offer Outside Price Band
  | unlisted (byte : { byte : UInt8 // byte ∉ FinraBboLuldIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinraBboLuldIndicator

def toByte : FinraBboLuldIndicator → UInt8
  | .limitUpLimitDownNotApplicable => 0x20
  | .finraBestBidAndFinraBestOfferAreExecutable => 0x41
  | .finraBestBidOutsidePriceBand => 0x42
  | .finraBestOfferOutsidePriceBand => 0x43
  | .finraBestBidAndFinraBestOfferOutsidePriceBand => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinraBboLuldIndicator :=
  if byte = 0x20 then .limitUpLimitDownNotApplicable
  else if byte = 0x41 then .finraBestBidAndFinraBestOfferAreExecutable
  else if byte = 0x42 then .finraBestBidOutsidePriceBand
  else if byte = 0x43 then .finraBestOfferOutsidePriceBand
  else .finraBestBidAndFinraBestOfferOutsidePriceBand

def ofByte (byte : UInt8) : FinraBboLuldIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinraBboLuldIndicator) : ofByte value.toByte = value := by
  cases value with
  | limitUpLimitDownNotApplicable => decide
  | finraBestBidAndFinraBestOfferAreExecutable => decide
  | finraBestBidOutsidePriceBand => decide
  | finraBestOfferOutsidePriceBand => decide
  | finraBestBidAndFinraBestOfferOutsidePriceBand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FinraBboLuldIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinraBboLuldIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FinraBboLuldIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FinraBboLuldIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FinraBboLuldIndicator

/-- SIP Block Timestamp: 8 bytes -/
structure SipBlockTimestamp where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace SipBlockTimestamp

def encode (message : SipBlockTimestamp) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (SipBlockTimestamp × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : SipBlockTimestamp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SipBlockTimestamp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SipBlockTimestamp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SipBlockTimestamp

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

/-- Symbol Reference Data Message: 205 bytes -/
structure SymbolReferenceDataMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  priorSecuritySymbol : Alpha 11
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  primaryListingMarketPreviousClosingPrice : BitVec 64
  consolidatedClosingPrice : BitVec 64
  roundLotSize : BitVec 16
  reserved : Alpha 1
  luldTier : LuldTier
  luldLeverageRatio : BitVec 32
  test : Test
  ipo : Ipo
  financialStatusIndicator : FinancialStatusIndicator
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  haltReason : Alpha 1
  instrumentType : InstrumentType
  secondReserved : Alpha 1
  thirdReserved : Alpha 1
  reserved128 : Alpha 128
  deriving DecidableEq, Repr

namespace SymbolReferenceDataMessage

def encode (message : SymbolReferenceDataMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.priorSecuritySymbol
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (encodeUInt 8 message.primaryListingMarketPreviousClosingPrice
    ++ (encodeUInt 8 message.consolidatedClosingPrice
    ++ (encodeUInt 2 message.roundLotSize
    ++ (Alpha.encode message.reserved
    ++ (LuldTier.encode message.luldTier
    ++ (encodeUInt 4 message.luldLeverageRatio
    ++ (Test.encode message.test
    ++ (Ipo.encode message.ipo
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (Alpha.encode message.haltReason
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.secondReserved
    ++ (Alpha.encode message.thirdReserved
    ++ (Alpha.encode message.reserved128))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SymbolReferenceDataMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (priorSecuritySymbol, bytes) ← Alpha.decode 11 bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (primaryListingMarketPreviousClosingPrice, bytes) ← decodeUInt 8 bytes
  let (consolidatedClosingPrice, bytes) ← decodeUInt 8 bytes
  let (roundLotSize, bytes) ← decodeUInt 2 bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (luldTier, bytes) ← LuldTier.decode bytes
  let (luldLeverageRatio, bytes) ← decodeUInt 4 bytes
  let (test, bytes) ← Test.decode bytes
  let (ipo, bytes) ← Ipo.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (haltReason, bytes) ← Alpha.decode 1 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (secondReserved, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved, bytes) ← Alpha.decode 1 bytes
  let (reserved128, bytes) ← Alpha.decode 128 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, priorSecuritySymbol, primaryListingMarketParticipantId, primaryListingMarketPreviousClosingPrice, consolidatedClosingPrice, roundLotSize, reserved, luldTier, luldLeverageRatio, test, ipo, financialStatusIndicator, shortSaleRestrictionIndicator, haltReason, instrumentType, secondReserved, thirdReserved, reserved128 }, bytes)

@[simp] theorem encode_length (message : SymbolReferenceDataMessage) : (encode message).length = 205 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, LuldTier.encode_length, Test.encode_length, Ipo.encode_length, FinancialStatusIndicator.encode_length, ShortSaleRestrictionIndicator.encode_length, InstrumentType.encode_length]

theorem encode_length_pos (message : SymbolReferenceDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolReferenceDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
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
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LuldTier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Test.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Ipo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolReferenceDataMessage

/-- Any Administrative Message Payload, selected by Administrative Message Type -/
inductive AdministrativeMessagePayload where
  | symbolReferenceDataMessage (message : SymbolReferenceDataMessage) -- "S" 0x53
  deriving DecidableEq, Repr

namespace AdministrativeMessagePayload

/-- The Administrative Message Type each message is sent under -/
def tag : AdministrativeMessagePayload → BitVec 8
  | .symbolReferenceDataMessage _ => 83

def encode : AdministrativeMessagePayload → List UInt8
  | .symbolReferenceDataMessage message => SymbolReferenceDataMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AdministrativeMessagePayload) : (encode message).length ≤ 205 := by
  cases message with
  | symbolReferenceDataMessage inner =>
    simp only [encode, SymbolReferenceDataMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AdministrativeMessagePayload × List UInt8) :=
  if tag = 83 then (SymbolReferenceDataMessage.decode bytes).map fun (message, rest) => (.symbolReferenceDataMessage message, rest)
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
theorem encode_length_le (message : AdministrativeMessage) : (encode message).length ≤ 206 := by
  unfold encode
  cases message.administrativeMessagePayload with
  | symbolReferenceDataMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, SymbolReferenceDataMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : AdministrativeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [AdministrativeMessagePayload.decode_encode, some_bind]
  rfl

end AdministrativeMessage

/-- Start Of Day Message: 22 bytes -/
structure StartOfDayMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StartOfDayMessage

def encode (message : StartOfDayMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (StartOfDayMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : StartOfDayMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StartOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfDayMessage

/-- Finra Close Message: 22 bytes -/
structure FinraCloseMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace FinraCloseMessage

def encode (message : FinraCloseMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (FinraCloseMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : FinraCloseMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FinraCloseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FinraCloseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FinraCloseMessage

/-- Reset Block Sequence Number Message: 22 bytes -/
structure ResetBlockSequenceNumberMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace ResetBlockSequenceNumberMessage

def encode (message : ResetBlockSequenceNumberMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (ResetBlockSequenceNumberMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : ResetBlockSequenceNumberMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ResetBlockSequenceNumberMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResetBlockSequenceNumberMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ResetBlockSequenceNumberMessage

/-- Finra Open Message: 22 bytes -/
structure FinraOpenMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace FinraOpenMessage

def encode (message : FinraOpenMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (FinraOpenMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : FinraOpenMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FinraOpenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FinraOpenMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FinraOpenMessage

/-- Disaster Recovery Data Center Activation Message: 22 bytes -/
structure DisasterRecoveryDataCenterActivationMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace DisasterRecoveryDataCenterActivationMessage

def encode (message : DisasterRecoveryDataCenterActivationMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (DisasterRecoveryDataCenterActivationMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : DisasterRecoveryDataCenterActivationMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DisasterRecoveryDataCenterActivationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisasterRecoveryDataCenterActivationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DisasterRecoveryDataCenterActivationMessage

/-- Line Integrity Message: 22 bytes -/
structure LineIntegrityMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LineIntegrityMessage

def encode (message : LineIntegrityMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (LineIntegrityMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : LineIntegrityMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LineIntegrityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LineIntegrityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LineIntegrityMessage

/-- End Of Day Message: 22 bytes -/
structure EndOfDayMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace EndOfDayMessage

def encode (message : EndOfDayMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber))))

def decode (bytes : List UInt8) : Option (EndOfDayMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : EndOfDayMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length]

theorem encode_length_pos (message : EndOfDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndOfDayMessage

/-- Any Control Message Payload, selected by Control Message Type -/
inductive ControlMessagePayload where
  | startOfDayMessage (message : StartOfDayMessage) -- "A" 0x41
  | finraCloseMessage (message : FinraCloseMessage) -- "C" 0x43
  | resetBlockSequenceNumberMessage (message : ResetBlockSequenceNumberMessage) -- "L" 0x4C
  | finraOpenMessage (message : FinraOpenMessage) -- "O" 0x4F
  | disasterRecoveryDataCenterActivationMessage (message : DisasterRecoveryDataCenterActivationMessage) -- "P" 0x50
  | lineIntegrityMessage (message : LineIntegrityMessage) -- "T" 0x54
  | endOfDayMessage (message : EndOfDayMessage) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace ControlMessagePayload

/-- The Control Message Type each message is sent under -/
def tag : ControlMessagePayload → BitVec 8
  | .startOfDayMessage _ => 65
  | .finraCloseMessage _ => 67
  | .resetBlockSequenceNumberMessage _ => 76
  | .finraOpenMessage _ => 79
  | .disasterRecoveryDataCenterActivationMessage _ => 80
  | .lineIntegrityMessage _ => 84
  | .endOfDayMessage _ => 90

def encode : ControlMessagePayload → List UInt8
  | .startOfDayMessage message => StartOfDayMessage.encode message
  | .finraCloseMessage message => FinraCloseMessage.encode message
  | .resetBlockSequenceNumberMessage message => ResetBlockSequenceNumberMessage.encode message
  | .finraOpenMessage message => FinraOpenMessage.encode message
  | .disasterRecoveryDataCenterActivationMessage message => DisasterRecoveryDataCenterActivationMessage.encode message
  | .lineIntegrityMessage message => LineIntegrityMessage.encode message
  | .endOfDayMessage message => EndOfDayMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ControlMessagePayload) : (encode message).length ≤ 22 := by
  cases message with
  | startOfDayMessage inner =>
    simp only [encode, StartOfDayMessage.encode_length]
    omega
  | finraCloseMessage inner =>
    simp only [encode, FinraCloseMessage.encode_length]
    omega
  | resetBlockSequenceNumberMessage inner =>
    simp only [encode, ResetBlockSequenceNumberMessage.encode_length]
    omega
  | finraOpenMessage inner =>
    simp only [encode, FinraOpenMessage.encode_length]
    omega
  | disasterRecoveryDataCenterActivationMessage inner =>
    simp only [encode, DisasterRecoveryDataCenterActivationMessage.encode_length]
    omega
  | lineIntegrityMessage inner =>
    simp only [encode, LineIntegrityMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [encode, EndOfDayMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ControlMessagePayload × List UInt8) :=
  if tag = 65 then (StartOfDayMessage.decode bytes).map fun (message, rest) => (.startOfDayMessage message, rest)
  else if tag = 67 then (FinraCloseMessage.decode bytes).map fun (message, rest) => (.finraCloseMessage message, rest)
  else if tag = 76 then (ResetBlockSequenceNumberMessage.decode bytes).map fun (message, rest) => (.resetBlockSequenceNumberMessage message, rest)
  else if tag = 79 then (FinraOpenMessage.decode bytes).map fun (message, rest) => (.finraOpenMessage message, rest)
  else if tag = 80 then (DisasterRecoveryDataCenterActivationMessage.decode bytes).map fun (message, rest) => (.disasterRecoveryDataCenterActivationMessage message, rest)
  else if tag = 84 then (LineIntegrityMessage.decode bytes).map fun (message, rest) => (.lineIntegrityMessage message, rest)
  else if tag = 90 then (EndOfDayMessage.decode bytes).map fun (message, rest) => (.endOfDayMessage message, rest)
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
theorem encode_length_le (message : ControlMessage) : (encode message).length ≤ 23 := by
  unfold encode
  cases message.controlMessagePayload with
  | startOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, StartOfDayMessage.encode_length]
    omega
  | finraCloseMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, FinraCloseMessage.encode_length]
    omega
  | resetBlockSequenceNumberMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, ResetBlockSequenceNumberMessage.encode_length]
    omega
  | finraOpenMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, FinraOpenMessage.encode_length]
    omega
  | disasterRecoveryDataCenterActivationMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, DisasterRecoveryDataCenterActivationMessage.encode_length]
    omega
  | lineIntegrityMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, LineIntegrityMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, EndOfDayMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ControlMessagePayload.decode_encode, some_bind]
  rfl

end ControlMessage

/-- Market Wide Circuit Breaker Decline Level Status Message: 47 bytes -/
structure MarketWideCircuitBreakerDeclineLevelStatusMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  mwcbLevel1 : BitVec 64
  mwcbLevel2 : BitVec 64
  mwcbLevel3 : BitVec 64
  reserved : Alpha 1
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerDeclineLevelStatusMessage

def encode (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (encodeUInt 8 message.mwcbLevel1
    ++ (encodeUInt 8 message.mwcbLevel2
    ++ (encodeUInt 8 message.mwcbLevel3
    ++ (Alpha.encode message.reserved))))))))

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerDeclineLevelStatusMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel1, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel2, bytes) ← decodeUInt 8 bytes
  let (mwcbLevel3, bytes) ← decodeUInt 8 bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, mwcbLevel1, mwcbLevel2, mwcbLevel3, reserved }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketWideCircuitBreakerDeclineLevelStatusMessage

/-- Market Wide Circuit Breaker Status Message: 24 bytes -/
structure MarketWideCircuitBreakerStatusMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  marketWideCircuitBreakerLevelIndicator : MarketWideCircuitBreakerLevelIndicator
  reserved : Alpha 1
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerStatusMessage

def encode (message : MarketWideCircuitBreakerStatusMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (MarketWideCircuitBreakerLevelIndicator.encode message.marketWideCircuitBreakerLevelIndicator
    ++ (Alpha.encode message.reserved))))))

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerStatusMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (marketWideCircuitBreakerLevelIndicator, bytes) ← MarketWideCircuitBreakerLevelIndicator.decode bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, marketWideCircuitBreakerLevelIndicator, reserved }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerStatusMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, MarketWideCircuitBreakerLevelIndicator.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketWideCircuitBreakerStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketWideCircuitBreakerStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MarketWideCircuitBreakerLevelIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketWideCircuitBreakerStatusMessage

/-- Any Market Status Message Payload, selected by Market Status Message Type -/
inductive MarketStatusMessagePayload where
  | marketWideCircuitBreakerDeclineLevelStatusMessage (message : MarketWideCircuitBreakerDeclineLevelStatusMessage) -- "K" 0x4B
  | marketWideCircuitBreakerStatusMessage (message : MarketWideCircuitBreakerStatusMessage) -- "L" 0x4C
  deriving DecidableEq, Repr

namespace MarketStatusMessagePayload

/-- The Market Status Message Type each message is sent under -/
def tag : MarketStatusMessagePayload → BitVec 8
  | .marketWideCircuitBreakerDeclineLevelStatusMessage _ => 75
  | .marketWideCircuitBreakerStatusMessage _ => 76

def encode : MarketStatusMessagePayload → List UInt8
  | .marketWideCircuitBreakerDeclineLevelStatusMessage message => MarketWideCircuitBreakerDeclineLevelStatusMessage.encode message
  | .marketWideCircuitBreakerStatusMessage message => MarketWideCircuitBreakerStatusMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MarketStatusMessagePayload) : (encode message).length ≤ 47 := by
  cases message with
  | marketWideCircuitBreakerDeclineLevelStatusMessage inner =>
    simp only [encode, MarketWideCircuitBreakerDeclineLevelStatusMessage.encode_length]
    omega
  | marketWideCircuitBreakerStatusMessage inner =>
    simp only [encode, MarketWideCircuitBreakerStatusMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (MarketStatusMessagePayload × List UInt8) :=
  if tag = 75 then (MarketWideCircuitBreakerDeclineLevelStatusMessage.decode bytes).map fun (message, rest) => (.marketWideCircuitBreakerDeclineLevelStatusMessage message, rest)
  else if tag = 76 then (MarketWideCircuitBreakerStatusMessage.decode bytes).map fun (message, rest) => (.marketWideCircuitBreakerStatusMessage message, rest)
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
theorem encode_length_le (message : MarketStatusMessage) : (encode message).length ≤ 48 := by
  unfold encode
  cases message.marketStatusMessagePayload with
  | marketWideCircuitBreakerDeclineLevelStatusMessage inner =>
    simp only [MarketStatusMessagePayload.encode, List.length_append, encodeUInt_length, MarketWideCircuitBreakerDeclineLevelStatusMessage.encode_length]
    omega
  | marketWideCircuitBreakerStatusMessage inner =>
    simp only [MarketStatusMessagePayload.encode, List.length_append, encodeUInt_length, MarketWideCircuitBreakerStatusMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : MarketStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MarketStatusMessagePayload.decode_encode, some_bind]
  rfl

end MarketStatusMessage

/-- Auction Status Message: 124 bytes -/
structure AuctionStatusMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  auctionCollarReferencePrice : BitVec 64
  auctionCollarUpperThresholdPrice : BitVec 64
  auctionCollarLowerThresholdPrice : BitVec 64
  numberOfExtensions : BitVec 8
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  reserved62 : Alpha 62
  deriving DecidableEq, Repr

namespace AuctionStatusMessage

def encode (message : AuctionStatusMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUInt 8 message.auctionCollarReferencePrice
    ++ (encodeUInt 8 message.auctionCollarUpperThresholdPrice
    ++ (encodeUInt 8 message.auctionCollarLowerThresholdPrice
    ++ (encodeUInt 1 message.numberOfExtensions
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (Alpha.encode message.reserved62))))))))))))))

def decode (bytes : List UInt8) : Option (AuctionStatusMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (auctionCollarReferencePrice, bytes) ← decodeUInt 8 bytes
  let (auctionCollarUpperThresholdPrice, bytes) ← decodeUInt 8 bytes
  let (auctionCollarLowerThresholdPrice, bytes) ← decodeUInt 8 bytes
  let (numberOfExtensions, bytes) ← decodeUInt 1 bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (reserved62, bytes) ← Alpha.decode 62 bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, auctionCollarReferencePrice, auctionCollarUpperThresholdPrice, auctionCollarLowerThresholdPrice, numberOfExtensions, shortSaleRestrictionIndicator, primaryListingMarketParticipantId, financialStatusIndicator, reserved62 }, bytes)

@[simp] theorem encode_length (message : AuctionStatusMessage) : (encode message).length = 124 := by
  unfold encode
  simp only [List.length_append, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length]

theorem encode_length_pos (message : AuctionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
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

/-- National Best Bid Long Appendage: 18 bytes -/
structure NationalBestBidLongAppendage where
  bestBidParticipantId : Alpha 1
  bestBidQuoteCondition : Alpha 1
  bestBidPriceLong : BitVec 64
  bestBidSizeLong : BitVec 32
  finraBestBidMarketMakerId : Alpha 4
  deriving DecidableEq, Repr

namespace NationalBestBidLongAppendage

def encode (message : NationalBestBidLongAppendage) : List UInt8 :=
  Alpha.encode message.bestBidParticipantId
    ++ (Alpha.encode message.bestBidQuoteCondition
    ++ (encodeUInt 8 message.bestBidPriceLong
    ++ (encodeUInt 4 message.bestBidSizeLong
    ++ (Alpha.encode message.finraBestBidMarketMakerId))))

def decode (bytes : List UInt8) : Option (NationalBestBidLongAppendage × List UInt8) := do
  let (bestBidParticipantId, bytes) ← Alpha.decode 1 bytes
  let (bestBidQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (bestBidPriceLong, bytes) ← decodeUInt 8 bytes
  let (bestBidSizeLong, bytes) ← decodeUInt 4 bytes
  let (finraBestBidMarketMakerId, bytes) ← Alpha.decode 4 bytes
  pure ({ bestBidParticipantId, bestBidQuoteCondition, bestBidPriceLong, bestBidSizeLong, finraBestBidMarketMakerId }, bytes)

@[simp] theorem encode_length (message : NationalBestBidLongAppendage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NationalBestBidLongAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NationalBestBidLongAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NationalBestBidLongAppendage

/-- National Best Offer Long Appendage: 18 bytes -/
structure NationalBestOfferLongAppendage where
  bestOfferParticipantId : Alpha 1
  bestOfferQuoteCondition : Alpha 1
  bestOfferPriceLong : BitVec 64
  bestOfferSizeLong : BitVec 32
  finraBestOfferMarketMakerId : Alpha 4
  deriving DecidableEq, Repr

namespace NationalBestOfferLongAppendage

def encode (message : NationalBestOfferLongAppendage) : List UInt8 :=
  Alpha.encode message.bestOfferParticipantId
    ++ (Alpha.encode message.bestOfferQuoteCondition
    ++ (encodeUInt 8 message.bestOfferPriceLong
    ++ (encodeUInt 4 message.bestOfferSizeLong
    ++ (Alpha.encode message.finraBestOfferMarketMakerId))))

def decode (bytes : List UInt8) : Option (NationalBestOfferLongAppendage × List UInt8) := do
  let (bestOfferParticipantId, bytes) ← Alpha.decode 1 bytes
  let (bestOfferQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (bestOfferPriceLong, bytes) ← decodeUInt 8 bytes
  let (bestOfferSizeLong, bytes) ← decodeUInt 4 bytes
  let (finraBestOfferMarketMakerId, bytes) ← Alpha.decode 4 bytes
  pure ({ bestOfferParticipantId, bestOfferQuoteCondition, bestOfferPriceLong, bestOfferSizeLong, finraBestOfferMarketMakerId }, bytes)

@[simp] theorem encode_length (message : NationalBestOfferLongAppendage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NationalBestOfferLongAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NationalBestOfferLongAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NationalBestOfferLongAppendage

/-- National Best Bid And Offer Long Appendage: 36 bytes -/
structure NationalBestBidAndOfferLongAppendage where
  bestBidParticipantId : Alpha 1
  bestBidQuoteCondition : Alpha 1
  bestBidPriceLong : BitVec 64
  bestBidSizeLong : BitVec 32
  finraBestBidMarketMakerId : Alpha 4
  bestOfferParticipantId : Alpha 1
  bestOfferQuoteCondition : Alpha 1
  bestOfferPriceLong : BitVec 64
  bestOfferSizeLong : BitVec 32
  finraBestOfferMarketMakerId : Alpha 4
  deriving DecidableEq, Repr

namespace NationalBestBidAndOfferLongAppendage

def encode (message : NationalBestBidAndOfferLongAppendage) : List UInt8 :=
  Alpha.encode message.bestBidParticipantId
    ++ (Alpha.encode message.bestBidQuoteCondition
    ++ (encodeUInt 8 message.bestBidPriceLong
    ++ (encodeUInt 4 message.bestBidSizeLong
    ++ (Alpha.encode message.finraBestBidMarketMakerId
    ++ (Alpha.encode message.bestOfferParticipantId
    ++ (Alpha.encode message.bestOfferQuoteCondition
    ++ (encodeUInt 8 message.bestOfferPriceLong
    ++ (encodeUInt 4 message.bestOfferSizeLong
    ++ (Alpha.encode message.finraBestOfferMarketMakerId)))))))))

def decode (bytes : List UInt8) : Option (NationalBestBidAndOfferLongAppendage × List UInt8) := do
  let (bestBidParticipantId, bytes) ← Alpha.decode 1 bytes
  let (bestBidQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (bestBidPriceLong, bytes) ← decodeUInt 8 bytes
  let (bestBidSizeLong, bytes) ← decodeUInt 4 bytes
  let (finraBestBidMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (bestOfferParticipantId, bytes) ← Alpha.decode 1 bytes
  let (bestOfferQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (bestOfferPriceLong, bytes) ← decodeUInt 8 bytes
  let (bestOfferSizeLong, bytes) ← decodeUInt 4 bytes
  let (finraBestOfferMarketMakerId, bytes) ← Alpha.decode 4 bytes
  pure ({ bestBidParticipantId, bestBidQuoteCondition, bestBidPriceLong, bestBidSizeLong, finraBestBidMarketMakerId, bestOfferParticipantId, bestOfferQuoteCondition, bestOfferPriceLong, bestOfferSizeLong, finraBestOfferMarketMakerId }, bytes)

@[simp] theorem encode_length (message : NationalBestBidAndOfferLongAppendage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NationalBestBidAndOfferLongAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NationalBestBidAndOfferLongAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NationalBestBidAndOfferLongAppendage

/-- National Best Bid Short Appendage: 5 bytes -/
structure NationalBestBidShortAppendage where
  bestBidParticipantId : Alpha 1
  bestBidPriceShort : BitVec 16
  bestBidSizeShort : BitVec 16
  deriving DecidableEq, Repr

namespace NationalBestBidShortAppendage

def encode (message : NationalBestBidShortAppendage) : List UInt8 :=
  Alpha.encode message.bestBidParticipantId
    ++ (encodeUInt 2 message.bestBidPriceShort
    ++ (encodeUInt 2 message.bestBidSizeShort))

def decode (bytes : List UInt8) : Option (NationalBestBidShortAppendage × List UInt8) := do
  let (bestBidParticipantId, bytes) ← Alpha.decode 1 bytes
  let (bestBidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bestBidSizeShort, bytes) ← decodeUInt 2 bytes
  pure ({ bestBidParticipantId, bestBidPriceShort, bestBidSizeShort }, bytes)

@[simp] theorem encode_length (message : NationalBestBidShortAppendage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NationalBestBidShortAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NationalBestBidShortAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NationalBestBidShortAppendage

/-- National Best Offer Short Appendage: 5 bytes -/
structure NationalBestOfferShortAppendage where
  bestOfferParticipantId : Alpha 1
  bestOfferPriceShort : BitVec 16
  bestOfferSizeShort : BitVec 16
  deriving DecidableEq, Repr

namespace NationalBestOfferShortAppendage

def encode (message : NationalBestOfferShortAppendage) : List UInt8 :=
  Alpha.encode message.bestOfferParticipantId
    ++ (encodeUInt 2 message.bestOfferPriceShort
    ++ (encodeUInt 2 message.bestOfferSizeShort))

def decode (bytes : List UInt8) : Option (NationalBestOfferShortAppendage × List UInt8) := do
  let (bestOfferParticipantId, bytes) ← Alpha.decode 1 bytes
  let (bestOfferPriceShort, bytes) ← decodeUInt 2 bytes
  let (bestOfferSizeShort, bytes) ← decodeUInt 2 bytes
  pure ({ bestOfferParticipantId, bestOfferPriceShort, bestOfferSizeShort }, bytes)

@[simp] theorem encode_length (message : NationalBestOfferShortAppendage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NationalBestOfferShortAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NationalBestOfferShortAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NationalBestOfferShortAppendage

/-- National Best Bid And Offer Short Appendage: 10 bytes -/
structure NationalBestBidAndOfferShortAppendage where
  bestBidParticipantId : Alpha 1
  bestBidPriceShort : BitVec 16
  bestBidSizeShort : BitVec 16
  bestOfferParticipantId : Alpha 1
  bestOfferPriceShort : BitVec 16
  bestOfferSizeShort : BitVec 16
  deriving DecidableEq, Repr

namespace NationalBestBidAndOfferShortAppendage

def encode (message : NationalBestBidAndOfferShortAppendage) : List UInt8 :=
  Alpha.encode message.bestBidParticipantId
    ++ (encodeUInt 2 message.bestBidPriceShort
    ++ (encodeUInt 2 message.bestBidSizeShort
    ++ (Alpha.encode message.bestOfferParticipantId
    ++ (encodeUInt 2 message.bestOfferPriceShort
    ++ (encodeUInt 2 message.bestOfferSizeShort)))))

def decode (bytes : List UInt8) : Option (NationalBestBidAndOfferShortAppendage × List UInt8) := do
  let (bestBidParticipantId, bytes) ← Alpha.decode 1 bytes
  let (bestBidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bestBidSizeShort, bytes) ← decodeUInt 2 bytes
  let (bestOfferParticipantId, bytes) ← Alpha.decode 1 bytes
  let (bestOfferPriceShort, bytes) ← decodeUInt 2 bytes
  let (bestOfferSizeShort, bytes) ← decodeUInt 2 bytes
  pure ({ bestBidParticipantId, bestBidPriceShort, bestBidSizeShort, bestOfferParticipantId, bestOfferPriceShort, bestOfferSizeShort }, bytes)

@[simp] theorem encode_length (message : NationalBestBidAndOfferShortAppendage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NationalBestBidAndOfferShortAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NationalBestBidAndOfferShortAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end NationalBestBidAndOfferShortAppendage

/-- National Bbo Indicator: 0 bytes -/
structure NationalBboAbsent where
  deriving DecidableEq, Repr

namespace NationalBboAbsent

def encode (_ : NationalBboAbsent) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (NationalBboAbsent × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : NationalBboAbsent) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : NationalBboAbsent) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end NationalBboAbsent

/-- The National Best Bid Long Appendage or National Best Offer Long Appendage or National Best Bid And Offer Long Appendage or National Best Bid Short Appendage or National Best Offer Short Appendage or National Best Bid And Offer Short Appendage the National Bbo Indicator says is attached, or none -/
inductive NationalBboChoice where
  | nationalBestBidLongAppendage (message : NationalBestBidLongAppendage) -- "Q" 0x51
  | nationalBestOfferLongAppendage (message : NationalBestOfferLongAppendage) -- "I" 0x49
  | nationalBestBidAndOfferLongAppendage (message : NationalBestBidAndOfferLongAppendage) -- "U" 0x55
  | nationalBestBidShortAppendage (message : NationalBestBidShortAppendage) -- "P" 0x50
  | nationalBestOfferShortAppendage (message : NationalBestOfferShortAppendage) -- "H" 0x48
  | nationalBestBidAndOfferShortAppendage (message : NationalBestBidAndOfferShortAppendage) -- "T" 0x54
  | quoteNotIncludedInBbo (message : NationalBboAbsent) -- " " 0x20
  | noBestBidChangeNoBestOfferChange (message : NationalBboAbsent) -- "A" 0x41
  | noBestBidChangeQuoteContainsBestOffer (message : NationalBboAbsent) -- "B" 0x42
  | noBestBidChangeBestOfferShortAppendage (message : NationalBboAbsent) -- "C" 0x43
  | noBestBidChangeBestOfferLongAppendage (message : NationalBboAbsent) -- "D" 0x44
  | noBestBidChangeNoBestOffer (message : NationalBboAbsent) -- "E" 0x45
  | quoteContainsBestBidNoBestOfferChange (message : NationalBboAbsent) -- "F" 0x46
  | quoteContainsBestBidQuoteContainsBestOffer (message : NationalBboAbsent) -- "G" 0x47
  | quoteContainsBestBidNoBestOffer (message : NationalBboAbsent) -- "J" 0x4A
  | noBestBidNoBestOfferChange (message : NationalBboAbsent) -- "K" 0x4B
  | noBestBidQuoteContainsBestOffer (message : NationalBboAbsent) -- "L" 0x4C
  | noBestBidBestOfferShortAppendage (message : NationalBboAbsent) -- "M" 0x4D
  | noBestBidBestOfferLongAppendage (message : NationalBboAbsent) -- "N" 0x4E
  | noBestBidNoBestOffer (message : NationalBboAbsent) -- "O" 0x4F
  | bestBidShortAppendageQuoteContainsBestOffer (message : NationalBboAbsent) -- "R" 0x52
  | bestBidLongAppendageQuoteContainsBestOffer (message : NationalBboAbsent) -- "S" 0x53
  | bestBidShortAppendageNoBestOffer (message : NationalBboAbsent) -- "V" 0x56
  | bestBidLongAppendageNoBestOffer (message : NationalBboAbsent) -- "W" 0x57
  deriving DecidableEq, Repr

namespace NationalBboChoice

/-- The National Bbo Indicator each message is sent under -/
def tag : NationalBboChoice → BitVec 8
  | .nationalBestBidLongAppendage _ => 81
  | .nationalBestOfferLongAppendage _ => 73
  | .nationalBestBidAndOfferLongAppendage _ => 85
  | .nationalBestBidShortAppendage _ => 80
  | .nationalBestOfferShortAppendage _ => 72
  | .nationalBestBidAndOfferShortAppendage _ => 84
  | .quoteNotIncludedInBbo _ => 32
  | .noBestBidChangeNoBestOfferChange _ => 65
  | .noBestBidChangeQuoteContainsBestOffer _ => 66
  | .noBestBidChangeBestOfferShortAppendage _ => 67
  | .noBestBidChangeBestOfferLongAppendage _ => 68
  | .noBestBidChangeNoBestOffer _ => 69
  | .quoteContainsBestBidNoBestOfferChange _ => 70
  | .quoteContainsBestBidQuoteContainsBestOffer _ => 71
  | .quoteContainsBestBidNoBestOffer _ => 74
  | .noBestBidNoBestOfferChange _ => 75
  | .noBestBidQuoteContainsBestOffer _ => 76
  | .noBestBidBestOfferShortAppendage _ => 77
  | .noBestBidBestOfferLongAppendage _ => 78
  | .noBestBidNoBestOffer _ => 79
  | .bestBidShortAppendageQuoteContainsBestOffer _ => 82
  | .bestBidLongAppendageQuoteContainsBestOffer _ => 83
  | .bestBidShortAppendageNoBestOffer _ => 86
  | .bestBidLongAppendageNoBestOffer _ => 87

def encode : NationalBboChoice → List UInt8
  | .nationalBestBidLongAppendage message => NationalBestBidLongAppendage.encode message
  | .nationalBestOfferLongAppendage message => NationalBestOfferLongAppendage.encode message
  | .nationalBestBidAndOfferLongAppendage message => NationalBestBidAndOfferLongAppendage.encode message
  | .nationalBestBidShortAppendage message => NationalBestBidShortAppendage.encode message
  | .nationalBestOfferShortAppendage message => NationalBestOfferShortAppendage.encode message
  | .nationalBestBidAndOfferShortAppendage message => NationalBestBidAndOfferShortAppendage.encode message
  | .quoteNotIncludedInBbo message => NationalBboAbsent.encode message
  | .noBestBidChangeNoBestOfferChange message => NationalBboAbsent.encode message
  | .noBestBidChangeQuoteContainsBestOffer message => NationalBboAbsent.encode message
  | .noBestBidChangeBestOfferShortAppendage message => NationalBboAbsent.encode message
  | .noBestBidChangeBestOfferLongAppendage message => NationalBboAbsent.encode message
  | .noBestBidChangeNoBestOffer message => NationalBboAbsent.encode message
  | .quoteContainsBestBidNoBestOfferChange message => NationalBboAbsent.encode message
  | .quoteContainsBestBidQuoteContainsBestOffer message => NationalBboAbsent.encode message
  | .quoteContainsBestBidNoBestOffer message => NationalBboAbsent.encode message
  | .noBestBidNoBestOfferChange message => NationalBboAbsent.encode message
  | .noBestBidQuoteContainsBestOffer message => NationalBboAbsent.encode message
  | .noBestBidBestOfferShortAppendage message => NationalBboAbsent.encode message
  | .noBestBidBestOfferLongAppendage message => NationalBboAbsent.encode message
  | .noBestBidNoBestOffer message => NationalBboAbsent.encode message
  | .bestBidShortAppendageQuoteContainsBestOffer message => NationalBboAbsent.encode message
  | .bestBidLongAppendageQuoteContainsBestOffer message => NationalBboAbsent.encode message
  | .bestBidShortAppendageNoBestOffer message => NationalBboAbsent.encode message
  | .bestBidLongAppendageNoBestOffer message => NationalBboAbsent.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : NationalBboChoice) : (encode message).length ≤ 36 := by
  cases message with
  | nationalBestBidLongAppendage inner =>
    simp only [encode, NationalBestBidLongAppendage.encode_length]
    omega
  | nationalBestOfferLongAppendage inner =>
    simp only [encode, NationalBestOfferLongAppendage.encode_length]
    omega
  | nationalBestBidAndOfferLongAppendage inner =>
    simp only [encode, NationalBestBidAndOfferLongAppendage.encode_length]
    omega
  | nationalBestBidShortAppendage inner =>
    simp only [encode, NationalBestBidShortAppendage.encode_length]
    omega
  | nationalBestOfferShortAppendage inner =>
    simp only [encode, NationalBestOfferShortAppendage.encode_length]
    omega
  | nationalBestBidAndOfferShortAppendage inner =>
    simp only [encode, NationalBestBidAndOfferShortAppendage.encode_length]
    omega
  | quoteNotIncludedInBbo inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOfferChange inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeQuoteContainsBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferShortAppendage inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferLongAppendage inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOfferChange inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidQuoteContainsBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOfferChange inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidQuoteContainsBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferShortAppendage inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferLongAppendage inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageQuoteContainsBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageQuoteContainsBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageNoBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageNoBestOffer inner =>
    simp only [encode, NationalBboAbsent.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (NationalBboChoice × List UInt8) :=
  if tag = 81 then (NationalBestBidLongAppendage.decode bytes).map fun (message, rest) => (.nationalBestBidLongAppendage message, rest)
  else if tag = 73 then (NationalBestOfferLongAppendage.decode bytes).map fun (message, rest) => (.nationalBestOfferLongAppendage message, rest)
  else if tag = 85 then (NationalBestBidAndOfferLongAppendage.decode bytes).map fun (message, rest) => (.nationalBestBidAndOfferLongAppendage message, rest)
  else if tag = 80 then (NationalBestBidShortAppendage.decode bytes).map fun (message, rest) => (.nationalBestBidShortAppendage message, rest)
  else if tag = 72 then (NationalBestOfferShortAppendage.decode bytes).map fun (message, rest) => (.nationalBestOfferShortAppendage message, rest)
  else if tag = 84 then (NationalBestBidAndOfferShortAppendage.decode bytes).map fun (message, rest) => (.nationalBestBidAndOfferShortAppendage message, rest)
  else if tag = 32 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.quoteNotIncludedInBbo message, rest)
  else if tag = 65 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidChangeNoBestOfferChange message, rest)
  else if tag = 66 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidChangeQuoteContainsBestOffer message, rest)
  else if tag = 67 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidChangeBestOfferShortAppendage message, rest)
  else if tag = 68 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidChangeBestOfferLongAppendage message, rest)
  else if tag = 69 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidChangeNoBestOffer message, rest)
  else if tag = 70 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.quoteContainsBestBidNoBestOfferChange message, rest)
  else if tag = 71 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.quoteContainsBestBidQuoteContainsBestOffer message, rest)
  else if tag = 74 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.quoteContainsBestBidNoBestOffer message, rest)
  else if tag = 75 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidNoBestOfferChange message, rest)
  else if tag = 76 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidQuoteContainsBestOffer message, rest)
  else if tag = 77 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidBestOfferShortAppendage message, rest)
  else if tag = 78 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidBestOfferLongAppendage message, rest)
  else if tag = 79 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.noBestBidNoBestOffer message, rest)
  else if tag = 82 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.bestBidShortAppendageQuoteContainsBestOffer message, rest)
  else if tag = 83 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.bestBidLongAppendageQuoteContainsBestOffer message, rest)
  else if tag = 86 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.bestBidShortAppendageNoBestOffer message, rest)
  else if tag = 87 then (NationalBboAbsent.decode bytes).map fun (message, rest) => (.bestBidLongAppendageNoBestOffer message, rest)
  else none

@[simp] theorem decode_encode (message : NationalBboChoice) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end NationalBboChoice

/-- Long Quote Message -/
structure LongQuoteMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  quoteCondition : QuoteCondition
  securityStatusIndicator : SecurityStatusIndicator
  bidPriceLowerLimitPriceBand : BitVec 64
  bidSizeLong : BitVec 32
  offerPriceUpperLimitPriceBand : BitVec 64
  offerSizeLong : BitVec 32
  retailInterestIndicator : RetailInterestIndicator
  settlementCondition : SettlementCondition
  marketCondition : MarketCondition
  finraMarketMakerId : Alpha 4
  finraBboIndicator : FinraBboIndicator
  timestamp2 : Timestamp2
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  sipGeneratedMessageIdentifier : SipGeneratedMessageIdentifier
  limitUpLimitDownLuldIndicator : LimitUpLimitDownLuldIndicator
  nationalBboLuldIndicator : NationalBboLuldIndicator
  nationalBboChoice : NationalBboChoice
  deriving DecidableEq, Repr

namespace LongQuoteMessage

def encode (message : LongQuoteMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (SecurityStatusIndicator.encode message.securityStatusIndicator
    ++ (encodeUInt 8 message.bidPriceLowerLimitPriceBand
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 8 message.offerPriceUpperLimitPriceBand
    ++ (encodeUInt 4 message.offerSizeLong
    ++ (RetailInterestIndicator.encode message.retailInterestIndicator
    ++ (SettlementCondition.encode message.settlementCondition
    ++ (MarketCondition.encode message.marketCondition
    ++ (Alpha.encode message.finraMarketMakerId
    ++ (FinraBboIndicator.encode message.finraBboIndicator
    ++ (Timestamp2.encode message.timestamp2
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (SipGeneratedMessageIdentifier.encode message.sipGeneratedMessageIdentifier
    ++ (LimitUpLimitDownLuldIndicator.encode message.limitUpLimitDownLuldIndicator
    ++ (NationalBboLuldIndicator.encode message.nationalBboLuldIndicator
    ++ (encodeUInt 1 (NationalBboChoice.tag message.nationalBboChoice)
    ++ (NationalBboChoice.encode message.nationalBboChoice))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (LongQuoteMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (securityStatusIndicator, bytes) ← SecurityStatusIndicator.decode bytes
  let (bidPriceLowerLimitPriceBand, bytes) ← decodeUInt 8 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (offerPriceUpperLimitPriceBand, bytes) ← decodeUInt 8 bytes
  let (offerSizeLong, bytes) ← decodeUInt 4 bytes
  let (retailInterestIndicator, bytes) ← RetailInterestIndicator.decode bytes
  let (settlementCondition, bytes) ← SettlementCondition.decode bytes
  let (marketCondition, bytes) ← MarketCondition.decode bytes
  let (finraMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBboIndicator, bytes) ← FinraBboIndicator.decode bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (sipGeneratedMessageIdentifier, bytes) ← SipGeneratedMessageIdentifier.decode bytes
  let (limitUpLimitDownLuldIndicator, bytes) ← LimitUpLimitDownLuldIndicator.decode bytes
  let (nationalBboLuldIndicator, bytes) ← NationalBboLuldIndicator.decode bytes
  let (nationalBboIndicator, bytes) ← decodeUInt 1 bytes
  let (nationalBboChoice, bytes) ← NationalBboChoice.decode nationalBboIndicator bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, quoteCondition, securityStatusIndicator, bidPriceLowerLimitPriceBand, bidSizeLong, offerPriceUpperLimitPriceBand, offerSizeLong, retailInterestIndicator, settlementCondition, marketCondition, finraMarketMakerId, finraBboIndicator, timestamp2, shortSaleRestrictionIndicator, primaryListingMarketParticipantId, financialStatusIndicator, sipGeneratedMessageIdentifier, limitUpLimitDownLuldIndicator, nationalBboLuldIndicator, nationalBboChoice }, bytes)

theorem encode_length_pos (message : LongQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ParticipantId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongQuoteMessage) : (encode message).length ≤ 119 := by
  unfold encode
  cases message.nationalBboChoice with
  | nationalBestBidLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestBidLongAppendage.encode_length]
    omega
  | nationalBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestOfferLongAppendage.encode_length]
    omega
  | nationalBestBidAndOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestBidAndOfferLongAppendage.encode_length]
    omega
  | nationalBestBidShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestBidShortAppendage.encode_length]
    omega
  | nationalBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestOfferShortAppendage.encode_length]
    omega
  | nationalBestBidAndOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestBidAndOfferShortAppendage.encode_length]
    omega
  | quoteNotIncludedInBbo inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, LimitUpLimitDownLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : LongQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RetailInterestIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinraBboIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SipGeneratedMessageIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LimitUpLimitDownLuldIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NationalBboLuldIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [NationalBboChoice.decode_encode, some_bind]
  rfl

end LongQuoteMessage

/-- Short Quote Message -/
structure ShortQuoteMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  offerPriceShort : BitVec 16
  offerSizeShort : BitVec 16
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  nationalBboChoice : NationalBboChoice
  deriving DecidableEq, Repr

namespace ShortQuoteMessage

def encode (message : ShortQuoteMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 2 message.bidPriceShort
    ++ (encodeUInt 2 message.bidSizeShort
    ++ (encodeUInt 2 message.offerPriceShort
    ++ (encodeUInt 2 message.offerSizeShort
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (encodeUInt 1 (NationalBboChoice.tag message.nationalBboChoice)
    ++ (NationalBboChoice.encode message.nationalBboChoice))))))))))))

def decode (bytes : List UInt8) : Option (ShortQuoteMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (bidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bidSizeShort, bytes) ← decodeUInt 2 bytes
  let (offerPriceShort, bytes) ← decodeUInt 2 bytes
  let (offerSizeShort, bytes) ← decodeUInt 2 bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (nationalBboIndicator, bytes) ← decodeUInt 1 bytes
  let (nationalBboChoice, bytes) ← NationalBboChoice.decode nationalBboIndicator bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, bidPriceShort, bidSizeShort, offerPriceShort, offerSizeShort, primaryListingMarketParticipantId, nationalBboChoice }, bytes)

theorem encode_length_pos (message : ShortQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ParticipantId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ShortQuoteMessage) : (encode message).length ≤ 79 := by
  unfold encode
  cases message.nationalBboChoice with
  | nationalBestBidLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBestBidLongAppendage.encode_length]
    omega
  | nationalBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBestOfferLongAppendage.encode_length]
    omega
  | nationalBestBidAndOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBestBidAndOfferLongAppendage.encode_length]
    omega
  | nationalBestBidShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBestBidShortAppendage.encode_length]
    omega
  | nationalBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBestOfferShortAppendage.encode_length]
    omega
  | nationalBestBidAndOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBestBidAndOfferShortAppendage.encode_length]
    omega
  | quoteNotIncludedInBbo inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, PrimaryListingMarketParticipantId.encode_length, NationalBboAbsent.encode_length]
    omega

@[simp] theorem decode_encode (message : ShortQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [NationalBboChoice.decode_encode, some_bind]
  rfl

end ShortQuoteMessage

/-- Special Long Quote Message -/
structure SpecialLongQuoteMessage where
  participantId : ParticipantId
  timestamp1 : Timestamp1
  messageId : BitVec 8
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 64
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  quoteCondition : QuoteCondition
  securityStatusIndicator : SecurityStatusIndicator
  bidPriceLong : BitVec 64
  bidSizeLong : BitVec 32
  offerPriceLong : BitVec 64
  offerSizeLong : BitVec 32
  retailInterestIndicator : RetailInterestIndicator
  settlementCondition : SettlementCondition
  marketCondition : MarketCondition
  finraMarketMakerId : Alpha 4
  finraBestBidQuoteCondition : Alpha 1
  finraBestBidPrice : BitVec 64
  finraBestBidSize : BitVec 32
  finraBestBidMarketMakerId : Alpha 4
  finraBestOfferQuoteCondition : Alpha 1
  finraBestOfferPrice : BitVec 64
  finraBestOfferSize : BitVec 32
  finraBestOfferMarketMakerId : Alpha 4
  timestamp2 : Timestamp2
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  primaryListingMarketParticipantId : PrimaryListingMarketParticipantId
  financialStatusIndicator : FinancialStatusIndicator
  sipGeneratedMessageIdentifier : SipGeneratedMessageIdentifier
  finraBboLuldIndicator : FinraBboLuldIndicator
  nationalBboLuldIndicator : NationalBboLuldIndicator
  nationalBboChoice : NationalBboChoice
  deriving DecidableEq, Repr

namespace SpecialLongQuoteMessage

def encode (message : SpecialLongQuoteMessage) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (SecurityStatusIndicator.encode message.securityStatusIndicator
    ++ (encodeUInt 8 message.bidPriceLong
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 8 message.offerPriceLong
    ++ (encodeUInt 4 message.offerSizeLong
    ++ (RetailInterestIndicator.encode message.retailInterestIndicator
    ++ (SettlementCondition.encode message.settlementCondition
    ++ (MarketCondition.encode message.marketCondition
    ++ (Alpha.encode message.finraMarketMakerId
    ++ (Alpha.encode message.finraBestBidQuoteCondition
    ++ (encodeUInt 8 message.finraBestBidPrice
    ++ (encodeUInt 4 message.finraBestBidSize
    ++ (Alpha.encode message.finraBestBidMarketMakerId
    ++ (Alpha.encode message.finraBestOfferQuoteCondition
    ++ (encodeUInt 8 message.finraBestOfferPrice
    ++ (encodeUInt 4 message.finraBestOfferSize
    ++ (Alpha.encode message.finraBestOfferMarketMakerId
    ++ (Timestamp2.encode message.timestamp2
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (PrimaryListingMarketParticipantId.encode message.primaryListingMarketParticipantId
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (SipGeneratedMessageIdentifier.encode message.sipGeneratedMessageIdentifier
    ++ (FinraBboLuldIndicator.encode message.finraBboLuldIndicator
    ++ (NationalBboLuldIndicator.encode message.nationalBboLuldIndicator
    ++ (encodeUInt 1 (NationalBboChoice.tag message.nationalBboChoice)
    ++ (NationalBboChoice.encode message.nationalBboChoice)))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpecialLongQuoteMessage × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (securityStatusIndicator, bytes) ← SecurityStatusIndicator.decode bytes
  let (bidPriceLong, bytes) ← decodeUInt 8 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (offerPriceLong, bytes) ← decodeUInt 8 bytes
  let (offerSizeLong, bytes) ← decodeUInt 4 bytes
  let (retailInterestIndicator, bytes) ← RetailInterestIndicator.decode bytes
  let (settlementCondition, bytes) ← SettlementCondition.decode bytes
  let (marketCondition, bytes) ← MarketCondition.decode bytes
  let (finraMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBestBidQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (finraBestBidPrice, bytes) ← decodeUInt 8 bytes
  let (finraBestBidSize, bytes) ← decodeUInt 4 bytes
  let (finraBestBidMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBestOfferQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (finraBestOfferPrice, bytes) ← decodeUInt 8 bytes
  let (finraBestOfferSize, bytes) ← decodeUInt 4 bytes
  let (finraBestOfferMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (primaryListingMarketParticipantId, bytes) ← PrimaryListingMarketParticipantId.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (sipGeneratedMessageIdentifier, bytes) ← SipGeneratedMessageIdentifier.decode bytes
  let (finraBboLuldIndicator, bytes) ← FinraBboLuldIndicator.decode bytes
  let (nationalBboLuldIndicator, bytes) ← NationalBboLuldIndicator.decode bytes
  let (nationalBboIndicator, bytes) ← decodeUInt 1 bytes
  let (nationalBboChoice, bytes) ← NationalBboChoice.decode nationalBboIndicator bytes
  pure ({ participantId, timestamp1, messageId, transactionId, participantReferenceNumber, securitySymbol, instrumentType, quoteCondition, securityStatusIndicator, bidPriceLong, bidSizeLong, offerPriceLong, offerSizeLong, retailInterestIndicator, settlementCondition, marketCondition, finraMarketMakerId, finraBestBidQuoteCondition, finraBestBidPrice, finraBestBidSize, finraBestBidMarketMakerId, finraBestOfferQuoteCondition, finraBestOfferPrice, finraBestOfferSize, finraBestOfferMarketMakerId, timestamp2, shortSaleRestrictionIndicator, primaryListingMarketParticipantId, financialStatusIndicator, sipGeneratedMessageIdentifier, finraBboLuldIndicator, nationalBboLuldIndicator, nationalBboChoice }, bytes)

theorem encode_length_pos (message : SpecialLongQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ParticipantId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SpecialLongQuoteMessage) : (encode message).length ≤ 152 := by
  unfold encode
  cases message.nationalBboChoice with
  | nationalBestBidLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestBidLongAppendage.encode_length]
    omega
  | nationalBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestOfferLongAppendage.encode_length]
    omega
  | nationalBestBidAndOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestBidAndOfferLongAppendage.encode_length]
    omega
  | nationalBestBidShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestBidShortAppendage.encode_length]
    omega
  | nationalBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestOfferShortAppendage.encode_length]
    omega
  | nationalBestBidAndOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBestBidAndOfferShortAppendage.encode_length]
    omega
  | quoteNotIncludedInBbo inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOfferChange inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferShortAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidBestOfferLongAppendage inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | noBestBidNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageQuoteContainsBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidShortAppendageNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega
  | bestBidLongAppendageNoBestOffer inner =>
    simp only [NationalBboChoice.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, Timestamp1.encode_length, encodeUInt_length, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, SecurityStatusIndicator.encode_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length, PrimaryListingMarketParticipantId.encode_length, FinancialStatusIndicator.encode_length, SipGeneratedMessageIdentifier.encode_length, FinraBboLuldIndicator.encode_length, NationalBboLuldIndicator.encode_length, NationalBboAbsent.encode_length]
    omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpecialLongQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RetailInterestIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCondition.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryListingMarketParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SipGeneratedMessageIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinraBboLuldIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NationalBboLuldIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [NationalBboChoice.decode_encode, some_bind]
  rfl

end SpecialLongQuoteMessage

/-- Any Quote Message Payload, selected by Quote Message Type -/
inductive QuoteMessagePayload where
  | auctionStatusMessage (message : AuctionStatusMessage) -- "A" 0x41
  | longQuoteMessage (message : LongQuoteMessage) -- "L" 0x4C
  | shortQuoteMessage (message : ShortQuoteMessage) -- "Q" 0x51
  | specialLongQuoteMessage (message : SpecialLongQuoteMessage) -- "S" 0x53
  deriving DecidableEq, Repr

namespace QuoteMessagePayload

/-- The Quote Message Type each message is sent under -/
def tag : QuoteMessagePayload → BitVec 8
  | .auctionStatusMessage _ => 65
  | .longQuoteMessage _ => 76
  | .shortQuoteMessage _ => 81
  | .specialLongQuoteMessage _ => 83

def encode : QuoteMessagePayload → List UInt8
  | .auctionStatusMessage message => AuctionStatusMessage.encode message
  | .longQuoteMessage message => LongQuoteMessage.encode message
  | .shortQuoteMessage message => ShortQuoteMessage.encode message
  | .specialLongQuoteMessage message => SpecialLongQuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : QuoteMessagePayload) : (encode message).length ≤ 152 := by
  cases message with
  | auctionStatusMessage inner =>
    simp only [encode, AuctionStatusMessage.encode_length]
    omega
  | longQuoteMessage inner =>
    have bound_inner := LongQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | shortQuoteMessage inner =>
    have bound_inner := ShortQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | specialLongQuoteMessage inner =>
    have bound_inner := SpecialLongQuoteMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (QuoteMessagePayload × List UInt8) :=
  if tag = 65 then (AuctionStatusMessage.decode bytes).map fun (message, rest) => (.auctionStatusMessage message, rest)
  else if tag = 76 then (LongQuoteMessage.decode bytes).map fun (message, rest) => (.longQuoteMessage message, rest)
  else if tag = 81 then (ShortQuoteMessage.decode bytes).map fun (message, rest) => (.shortQuoteMessage message, rest)
  else if tag = 83 then (SpecialLongQuoteMessage.decode bytes).map fun (message, rest) => (.specialLongQuoteMessage message, rest)
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
theorem encode_length_le (message : QuoteMessage) : (encode message).length ≤ 153 := by
  unfold encode
  cases message.quoteMessagePayload with
  | auctionStatusMessage inner =>
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length, AuctionStatusMessage.encode_length]
    omega
  | longQuoteMessage inner =>
    have bound_inner := LongQuoteMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | shortQuoteMessage inner =>
    have bound_inner := ShortQuoteMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | specialLongQuoteMessage inner =>
    have bound_inner := SpecialLongQuoteMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : QuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [QuoteMessagePayload.decode_encode, some_bind]
  rfl

end QuoteMessage

/-- Any Category Payload, selected by Message Category -/
inductive CategoryPayload where
  | administrativeMessage (message : AdministrativeMessage) -- "A" 0x41
  | controlMessage (message : ControlMessage) -- "C" 0x43
  | marketStatusMessage (message : MarketStatusMessage) -- "M" 0x4D
  | quoteMessage (message : QuoteMessage) -- "Q" 0x51
  deriving DecidableEq, Repr

namespace CategoryPayload

/-- The Message Category each message is sent under -/
def tag : CategoryPayload → BitVec 8
  | .administrativeMessage _ => 65
  | .controlMessage _ => 67
  | .marketStatusMessage _ => 77
  | .quoteMessage _ => 81

def encode : CategoryPayload → List UInt8
  | .administrativeMessage message => AdministrativeMessage.encode message
  | .controlMessage message => ControlMessage.encode message
  | .marketStatusMessage message => MarketStatusMessage.encode message
  | .quoteMessage message => QuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : CategoryPayload) : (encode message).length ≤ 206 := by
  cases message with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega
  | controlMessage inner =>
    have bound_inner := ControlMessage.encode_length_le inner
    simp only [encode]
    omega
  | marketStatusMessage inner =>
    have bound_inner := MarketStatusMessage.encode_length_le inner
    simp only [encode]
    omega
  | quoteMessage inner =>
    have bound_inner := QuoteMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (CategoryPayload × List UInt8) :=
  if tag = 65 then (AdministrativeMessage.decode bytes).map fun (message, rest) => (.administrativeMessage message, rest)
  else if tag = 67 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage message, rest)
  else if tag = 77 then (MarketStatusMessage.decode bytes).map fun (message, rest) => (.marketStatusMessage message, rest)
  else if tag = 81 then (QuoteMessage.decode bytes).map fun (message, rest) => (.quoteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : CategoryPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end CategoryPayload

/-- Message -/
structure Message where
  messageLength : BitVec 16
  categoryPayload : CategoryPayload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUInt 2 message.messageLength
    ++ (encodeUInt 1 (CategoryPayload.tag message.categoryPayload)
    ++ (CategoryPayload.encode message.categoryPayload))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (messageCategory, bytes) ← decodeUInt 1 bytes
  let (categoryPayload, bytes) ← CategoryPayload.decode messageCategory bytes
  pure ({ messageLength, categoryPayload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 209 := by
  unfold encode
  cases message.categoryPayload with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | controlMessage inner =>
    have bound_inner := ControlMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | marketStatusMessage inner =>
    have bound_inner := MarketStatusMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | quoteMessage inner =>
    have bound_inner := QuoteMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CategoryPayload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  version : BitVec 8
  blockSize : BitVec 16
  dataFeedIndicator : Alpha 1
  retransmissionIndicator : Alpha 1
  blockSequenceNumber : BitVec 32
  sipBlockTimestamp : SipBlockTimestamp
  blockChecksum : BitVec 16
  message : Bounded 1 Message
  blockPadByte : Capped 1
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.version
    ++ (encodeUInt 2 message.blockSize
    ++ (Alpha.encode message.dataFeedIndicator
    ++ (Alpha.encode message.retransmissionIndicator
    ++ (encodeUInt 4 message.blockSequenceNumber
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (SipBlockTimestamp.encode message.sipBlockTimestamp
    ++ (encodeUInt 2 message.blockChecksum
    ++ (encodeMany Message.encode message.message.val
    ++ (message.blockPadByte.val)))))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (version, bytes) ← decodeUInt 1 bytes
  let (blockSize, bytes) ← decodeUInt 2 bytes
  let (dataFeedIndicator, bytes) ← Alpha.decode 1 bytes
  let (retransmissionIndicator, bytes) ← Alpha.decode 1 bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (messagesInBlock, bytes) ← decodeUInt 1 bytes
  let (sipBlockTimestamp, bytes) ← SipBlockTimestamp.decode bytes
  let (blockChecksum, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messagesInBlock.toNat bytes
  let blockPadByte_ := bytes
  if fits_message : message_.length < 256 ^ 1 then
    if fits_blockPadByte : blockPadByte_.length ≤ 1 then
      pure { version, blockSize, dataFeedIndicator, retransmissionIndicator, blockSequenceNumber, sipBlockTimestamp, blockChecksum, message := ⟨message_, fits_message⟩, blockPadByte := ⟨blockPadByte_, fits_blockPadByte⟩ }
    else none
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 53316 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 209 Message.encode_length_le message.message.val
  have bound_blockPadByte := message.blockPadByte.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SipBlockTimestamp.encode_length]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SipBlockTimestamp.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt, dite_eq_left message.blockPadByte.length_le]
  rfl

end Packet

end Omi.SiacCqsOutputCtaV210A
