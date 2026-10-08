import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Basic Plus v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesBasicplusItchV10

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4D, 0x45, 0x43]

inductive EventCode where
  | startOfConsolidatedMarketTransmissions -- Start Of Consolidated Market Transmissions
  | startOfSystemHours -- Start Of System Hours
  | startOfRegularMarketHours -- Start Of Regular Market Hours
  | endOfRegularMarketHours -- End Of Regular Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfTransmissions -- End Of Transmissions
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfConsolidatedMarketTransmissions => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfRegularMarketHours => 0x51
  | .endOfRegularMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfTransmissions => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfConsolidatedMarketTransmissions
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfRegularMarketHours
  else if byte = 0x4D then .endOfRegularMarketHours
  else if byte = 0x45 then .endOfSystemHours
  else .endOfTransmissions

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfConsolidatedMarketTransmissions => decide
  | startOfSystemHours => decide
  | startOfRegularMarketHours => decide
  | endOfRegularMarketHours => decide
  | endOfSystemHours => decide
  | endOfTransmissions => decide
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

/-- Trading State: one byte code -/
def TradingState.codes : List UInt8 :=
  [0x48, 0x50, 0x51, 0x54]

inductive TradingState where
  | halted -- Halted
  | paused -- Paused
  | quotationOnlyPeriod -- Quotation Only Period
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .halted => 0x48
  | .paused => 0x50
  | .quotationOnlyPeriod => 0x51
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x48 then .halted
  else if byte = 0x50 then .paused
  else if byte = 0x51 then .quotationOnlyPeriod
  else .trading

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | paused => decide
  | quotationOnlyPeriod => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingState

/-- Reg Sho Action: one byte code -/
def RegShoAction.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive RegShoAction where
  | noPriceTest -- No Price Test
  | regShoShortSalePriceTestRestriction -- Reg Sho Short Sale Price Test Restriction
  | testRestrictionRemains -- Test Restriction Remains
  | unlisted (byte : { byte : UInt8 // byte ∉ RegShoAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RegShoAction

def toByte : RegShoAction → UInt8
  | .noPriceTest => 0x30
  | .regShoShortSalePriceTestRestriction => 0x31
  | .testRestrictionRemains => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RegShoAction :=
  if byte = 0x30 then .noPriceTest
  else if byte = 0x31 then .regShoShortSalePriceTestRestriction
  else .testRestrictionRemains

def ofByte (byte : UInt8) : RegShoAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RegShoAction) : ofByte value.toByte = value := by
  cases value with
  | noPriceTest => decide
  | regShoShortSalePriceTestRestriction => decide
  | testRestrictionRemains => decide
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

/-- Market Category: one byte code -/
def MarketCategory.codes : List UInt8 :=
  [0x51, 0x47, 0x53, 0x4E, 0x41, 0x50, 0x4D, 0x5A, 0x56, 0x20]

inductive MarketCategory where
  | nasdaqGlobalSelectMarket -- Nasdaq Global Select Market
  | nasdaqGlobalMarket -- Nasdaq Global Market
  | nasdaqCapitalMarket -- Nasdaq Capital Market
  | nyse -- Nyse
  | nyseAmerican -- Nyse American
  | nyseArca -- Nyse Arca
  | nyseTexas -- Nyse Texas
  | batsZ -- Bats Z
  | investorsExchange -- Investors Exchange
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCategory

def toByte : MarketCategory → UInt8
  | .nasdaqGlobalSelectMarket => 0x51
  | .nasdaqGlobalMarket => 0x47
  | .nasdaqCapitalMarket => 0x53
  | .nyse => 0x4E
  | .nyseAmerican => 0x41
  | .nyseArca => 0x50
  | .nyseTexas => 0x4D
  | .batsZ => 0x5A
  | .investorsExchange => 0x56
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCategory :=
  if byte = 0x51 then .nasdaqGlobalSelectMarket
  else if byte = 0x47 then .nasdaqGlobalMarket
  else if byte = 0x53 then .nasdaqCapitalMarket
  else if byte = 0x4E then .nyse
  else if byte = 0x41 then .nyseAmerican
  else if byte = 0x50 then .nyseArca
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x5A then .batsZ
  else if byte = 0x56 then .investorsExchange
  else .notAvailable

def ofByte (byte : UInt8) : MarketCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCategory) : ofByte value.toByte = value := by
  cases value with
  | nasdaqGlobalSelectMarket => decide
  | nasdaqGlobalMarket => decide
  | nasdaqCapitalMarket => decide
  | nyse => decide
  | nyseAmerican => decide
  | nyseArca => decide
  | nyseTexas => decide
  | batsZ => decide
  | investorsExchange => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCategory

/-- Financial Status Indicator: one byte code -/
def FinancialStatusIndicator.codes : List UInt8 :=
  [0x44, 0x45, 0x51, 0x53, 0x47, 0x48, 0x4A, 0x4B, 0x43, 0x4E, 0x20]

inductive FinancialStatusIndicator where
  | deficient -- Deficient
  | delinquent -- Delinquent
  | bankrupt -- Bankrupt
  | suspended -- Suspended
  | deficientAndBankrupt -- Deficient And Bankrupt
  | deficientAndDelinquent -- Deficient And Delinquent
  | delinquentAndBankrupt -- Delinquent And Bankrupt
  | deficientDelinquentAndBankrupt -- Deficient Delinquent And Bankrupt
  | creationsAndRedemptionsSuspended -- Creations And Redemptions Suspended
  | normal -- Normal
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ FinancialStatusIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinancialStatusIndicator

def toByte : FinancialStatusIndicator → UInt8
  | .deficient => 0x44
  | .delinquent => 0x45
  | .bankrupt => 0x51
  | .suspended => 0x53
  | .deficientAndBankrupt => 0x47
  | .deficientAndDelinquent => 0x48
  | .delinquentAndBankrupt => 0x4A
  | .deficientDelinquentAndBankrupt => 0x4B
  | .creationsAndRedemptionsSuspended => 0x43
  | .normal => 0x4E
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinancialStatusIndicator :=
  if byte = 0x44 then .deficient
  else if byte = 0x45 then .delinquent
  else if byte = 0x51 then .bankrupt
  else if byte = 0x53 then .suspended
  else if byte = 0x47 then .deficientAndBankrupt
  else if byte = 0x48 then .deficientAndDelinquent
  else if byte = 0x4A then .delinquentAndBankrupt
  else if byte = 0x4B then .deficientDelinquentAndBankrupt
  else if byte = 0x43 then .creationsAndRedemptionsSuspended
  else if byte = 0x4E then .normal
  else .notAvailable

def ofByte (byte : UInt8) : FinancialStatusIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinancialStatusIndicator) : ofByte value.toByte = value := by
  cases value with
  | deficient => decide
  | delinquent => decide
  | bankrupt => decide
  | suspended => decide
  | deficientAndBankrupt => decide
  | deficientAndDelinquent => decide
  | delinquentAndBankrupt => decide
  | deficientDelinquentAndBankrupt => decide
  | creationsAndRedemptionsSuspended => decide
  | normal => decide
  | notAvailable => decide
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

/-- Round Lots Only: one byte code -/
def RoundLotsOnly.codes : List UInt8 :=
  [0x59, 0x4E]

inductive RoundLotsOnly where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ RoundLotsOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RoundLotsOnly

def toByte : RoundLotsOnly → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RoundLotsOnly :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : RoundLotsOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RoundLotsOnly) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RoundLotsOnly) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RoundLotsOnly × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RoundLotsOnly) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RoundLotsOnly) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RoundLotsOnly

/-- Issue Classification: one byte code -/
def IssueClassification.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x46, 0x49, 0x4C, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57]

inductive IssueClassification where
  | americanDepositaryShare -- American Depositary Share
  | bond -- Bond
  | commonStock -- Common Stock
  | depositoryReceipt -- Depository Receipt
  | sec144A -- Sec 144 A
  | limitedPartnership -- Limited Partnership
  | notes -- Notes
  | ordinaryShare -- Ordinary Share
  | preferredStock -- Preferred Stock
  | otherSecurities -- Other Securities
  | right -- Right
  | sharesOfBeneficialInterest -- Shares Of Beneficial Interest
  | convertibleDebenture -- Convertible Debenture
  | unit -- Unit
  | unitsOfBeneficialInterest -- Units Of Beneficial Interest
  | warrant -- Warrant
  | unlisted (byte : { byte : UInt8 // byte ∉ IssueClassification.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IssueClassification

def toByte : IssueClassification → UInt8
  | .americanDepositaryShare => 0x41
  | .bond => 0x42
  | .commonStock => 0x43
  | .depositoryReceipt => 0x46
  | .sec144A => 0x49
  | .limitedPartnership => 0x4C
  | .notes => 0x4E
  | .ordinaryShare => 0x4F
  | .preferredStock => 0x50
  | .otherSecurities => 0x51
  | .right => 0x52
  | .sharesOfBeneficialInterest => 0x53
  | .convertibleDebenture => 0x54
  | .unit => 0x55
  | .unitsOfBeneficialInterest => 0x56
  | .warrant => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IssueClassification :=
  if byte = 0x41 then .americanDepositaryShare
  else if byte = 0x42 then .bond
  else if byte = 0x43 then .commonStock
  else if byte = 0x46 then .depositoryReceipt
  else if byte = 0x49 then .sec144A
  else if byte = 0x4C then .limitedPartnership
  else if byte = 0x4E then .notes
  else if byte = 0x4F then .ordinaryShare
  else if byte = 0x50 then .preferredStock
  else if byte = 0x51 then .otherSecurities
  else if byte = 0x52 then .right
  else if byte = 0x53 then .sharesOfBeneficialInterest
  else if byte = 0x54 then .convertibleDebenture
  else if byte = 0x55 then .unit
  else if byte = 0x56 then .unitsOfBeneficialInterest
  else .warrant

def ofByte (byte : UInt8) : IssueClassification :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IssueClassification) : ofByte value.toByte = value := by
  cases value with
  | americanDepositaryShare => decide
  | bond => decide
  | commonStock => decide
  | depositoryReceipt => decide
  | sec144A => decide
  | limitedPartnership => decide
  | notes => decide
  | ordinaryShare => decide
  | preferredStock => decide
  | otherSecurities => decide
  | right => decide
  | sharesOfBeneficialInterest => decide
  | convertibleDebenture => decide
  | unit => decide
  | unitsOfBeneficialInterest => decide
  | warrant => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IssueClassification) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IssueClassification × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IssueClassification) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IssueClassification) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IssueClassification

/-- Authenticity: one byte code -/
def Authenticity.codes : List UInt8 :=
  [0x50, 0x54]

inductive Authenticity where
  | liveProduction -- Live Production
  | test -- Test
  | unlisted (byte : { byte : UInt8 // byte ∉ Authenticity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Authenticity

def toByte : Authenticity → UInt8
  | .liveProduction => 0x50
  | .test => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Authenticity :=
  if byte = 0x50 then .liveProduction
  else .test

def ofByte (byte : UInt8) : Authenticity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Authenticity) : ofByte value.toByte = value := by
  cases value with
  | liveProduction => decide
  | test => decide
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
  | restricted -- Restricted
  | notRestricted -- Not Restricted
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSaleThresholdIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSaleThresholdIndicator

def toByte : ShortSaleThresholdIndicator → UInt8
  | .restricted => 0x59
  | .notRestricted => 0x4E
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSaleThresholdIndicator :=
  if byte = 0x59 then .restricted
  else if byte = 0x4E then .notRestricted
  else .notAvailable

def ofByte (byte : UInt8) : ShortSaleThresholdIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSaleThresholdIndicator) : ofByte value.toByte = value := by
  cases value with
  | restricted => decide
  | notRestricted => decide
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

/-- Ipo Flag: one byte code -/
def IpoFlag.codes : List UInt8 :=
  [0x59, 0x4E, 0x5A, 0x20]

inductive IpoFlag where
  | setUpForIpoRelease -- Set Up For Ipo Release
  | notSetUpForIpoRelease -- Not Set Up For Ipo Release
  | nonIpoNewListedSecurity -- Non Ipo New Listed Security
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ IpoFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IpoFlag

def toByte : IpoFlag → UInt8
  | .setUpForIpoRelease => 0x59
  | .notSetUpForIpoRelease => 0x4E
  | .nonIpoNewListedSecurity => 0x5A
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IpoFlag :=
  if byte = 0x59 then .setUpForIpoRelease
  else if byte = 0x4E then .notSetUpForIpoRelease
  else if byte = 0x5A then .nonIpoNewListedSecurity
  else .notAvailable

def ofByte (byte : UInt8) : IpoFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IpoFlag) : ofByte value.toByte = value := by
  cases value with
  | setUpForIpoRelease => decide
  | notSetUpForIpoRelease => decide
  | nonIpoNewListedSecurity => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IpoFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IpoFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IpoFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IpoFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IpoFlag

/-- Luld Reference Price Tier: one byte code -/
def LuldReferencePriceTier.codes : List UInt8 :=
  [0x31, 0x32, 0x20]

inductive LuldReferencePriceTier where
  | tier1 -- Tier 1
  | tier2 -- Tier 2
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ LuldReferencePriceTier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LuldReferencePriceTier

def toByte : LuldReferencePriceTier → UInt8
  | .tier1 => 0x31
  | .tier2 => 0x32
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LuldReferencePriceTier :=
  if byte = 0x31 then .tier1
  else if byte = 0x32 then .tier2
  else .notAvailable

def ofByte (byte : UInt8) : LuldReferencePriceTier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LuldReferencePriceTier) : ofByte value.toByte = value := by
  cases value with
  | tier1 => decide
  | tier2 => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LuldReferencePriceTier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LuldReferencePriceTier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LuldReferencePriceTier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LuldReferencePriceTier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LuldReferencePriceTier

/-- Etp Flag: one byte code -/
def EtpFlag.codes : List UInt8 :=
  [0x59, 0x4E, 0x20]

inductive EtpFlag where
  | etp -- Etp
  | notEtp -- Not Etp
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ EtpFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EtpFlag

def toByte : EtpFlag → UInt8
  | .etp => 0x59
  | .notEtp => 0x4E
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EtpFlag :=
  if byte = 0x59 then .etp
  else if byte = 0x4E then .notEtp
  else .notAvailable

def ofByte (byte : UInt8) : EtpFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EtpFlag) : ofByte value.toByte = value := by
  cases value with
  | etp => decide
  | notEtp => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EtpFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EtpFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EtpFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EtpFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EtpFlag

/-- Inverse Indicator: one byte code -/
def InverseIndicator.codes : List UInt8 :=
  [0x59, 0x4E]

inductive InverseIndicator where
  | inverseEtp -- Inverse Etp
  | notInverseEtp -- Not Inverse Etp
  | unlisted (byte : { byte : UInt8 // byte ∉ InverseIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InverseIndicator

def toByte : InverseIndicator → UInt8
  | .inverseEtp => 0x59
  | .notInverseEtp => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InverseIndicator :=
  if byte = 0x59 then .inverseEtp
  else .notInverseEtp

def ofByte (byte : UInt8) : InverseIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InverseIndicator) : ofByte value.toByte = value := by
  cases value with
  | inverseEtp => decide
  | notInverseEtp => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InverseIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InverseIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InverseIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InverseIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InverseIndicator

/-- Breached Level: one byte code -/
def BreachedLevel.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive BreachedLevel where
  | level1 -- Level 1
  | level2 -- Level 2
  | level3 -- Level 3
  | unlisted (byte : { byte : UInt8 // byte ∉ BreachedLevel.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BreachedLevel

def toByte : BreachedLevel → UInt8
  | .level1 => 0x31
  | .level2 => 0x32
  | .level3 => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BreachedLevel :=
  if byte = 0x31 then .level1
  else if byte = 0x32 then .level2
  else .level3

def ofByte (byte : UInt8) : BreachedLevel :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BreachedLevel) : ofByte value.toByte = value := by
  cases value with
  | level1 => decide
  | level2 => decide
  | level3 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BreachedLevel) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BreachedLevel × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BreachedLevel) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BreachedLevel) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BreachedLevel

/-- Ipo Quotation Release Qualifier: one byte code -/
def IpoQuotationReleaseQualifier.codes : List UInt8 :=
  [0x41, 0x43]

inductive IpoQuotationReleaseQualifier where
  | anticipatedQuotationReleaseTime -- Anticipated Quotation Release Time
  | ipoReleaseCanceledOrPostponed -- Ipo Release Canceled Or Postponed
  | unlisted (byte : { byte : UInt8 // byte ∉ IpoQuotationReleaseQualifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IpoQuotationReleaseQualifier

def toByte : IpoQuotationReleaseQualifier → UInt8
  | .anticipatedQuotationReleaseTime => 0x41
  | .ipoReleaseCanceledOrPostponed => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IpoQuotationReleaseQualifier :=
  if byte = 0x41 then .anticipatedQuotationReleaseTime
  else .ipoReleaseCanceledOrPostponed

def ofByte (byte : UInt8) : IpoQuotationReleaseQualifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IpoQuotationReleaseQualifier) : ofByte value.toByte = value := by
  cases value with
  | anticipatedQuotationReleaseTime => decide
  | ipoReleaseCanceledOrPostponed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IpoQuotationReleaseQualifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IpoQuotationReleaseQualifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IpoQuotationReleaseQualifier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IpoQuotationReleaseQualifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IpoQuotationReleaseQualifier

/-- Market Code: one byte code -/
def MarketCode.codes : List UInt8 :=
  [0x51, 0x42, 0x58]

inductive MarketCode where
  | nasdaq -- Nasdaq
  | nasdaqTexas -- Nasdaq Texas
  | psx -- Psx
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCode

def toByte : MarketCode → UInt8
  | .nasdaq => 0x51
  | .nasdaqTexas => 0x42
  | .psx => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCode :=
  if byte = 0x51 then .nasdaq
  else if byte = 0x42 then .nasdaqTexas
  else .psx

def ofByte (byte : UInt8) : MarketCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCode) : ofByte value.toByte = value := by
  cases value with
  | nasdaq => decide
  | nasdaqTexas => decide
  | psx => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCode

/-- Operational Halt Action: one byte code -/
def OperationalHaltAction.codes : List UInt8 :=
  [0x48, 0x54]

inductive OperationalHaltAction where
  | halted -- Halted
  | tradingResumed -- Trading Resumed
  | unlisted (byte : { byte : UInt8 // byte ∉ OperationalHaltAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OperationalHaltAction

def toByte : OperationalHaltAction → UInt8
  | .halted => 0x48
  | .tradingResumed => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OperationalHaltAction :=
  if byte = 0x48 then .halted
  else .tradingResumed

def ofByte (byte : UInt8) : OperationalHaltAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OperationalHaltAction) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | tradingResumed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OperationalHaltAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OperationalHaltAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OperationalHaltAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OperationalHaltAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OperationalHaltAction

/-- System Event Message: 9 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 64
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (EventCode.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ timestamp, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 9 := by
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
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Consolidated Quotation Message: 42 bytes -/
structure ConsolidatedQuotationMessage where
  timestamp : BitVec 64
  stock : Alpha 8
  bestBidPrice : BitVec 64
  bestBidSize : BitVec 32
  bestOfferPrice : BitVec 64
  bestOfferSize : BitVec 32
  bestBidExchanges : BitVec 8
  bestOfferExchanges : BitVec 8
  deriving DecidableEq, Repr

namespace ConsolidatedQuotationMessage

def encode (message : ConsolidatedQuotationMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 8 message.bestBidPrice
    ++ (encodeUInt 4 message.bestBidSize
    ++ (encodeUInt 8 message.bestOfferPrice
    ++ (encodeUInt 4 message.bestOfferSize
    ++ (encodeUInt 1 message.bestBidExchanges
    ++ (encodeUInt 1 message.bestOfferExchanges)))))))

def decode (bytes : List UInt8) : Option (ConsolidatedQuotationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (bestBidPrice, bytes) ← decodeUInt 8 bytes
  let (bestBidSize, bytes) ← decodeUInt 4 bytes
  let (bestOfferPrice, bytes) ← decodeUInt 8 bytes
  let (bestOfferSize, bytes) ← decodeUInt 4 bytes
  let (bestBidExchanges, bytes) ← decodeUInt 1 bytes
  let (bestOfferExchanges, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, stock, bestBidPrice, bestBidSize, bestOfferPrice, bestOfferSize, bestBidExchanges, bestOfferExchanges }, bytes)

@[simp] theorem encode_length (message : ConsolidatedQuotationMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ConsolidatedQuotationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedQuotationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ConsolidatedQuotationMessage

/-- Retail Price Improvement Message: 18 bytes -/
structure RetailPriceImprovementMessage where
  timestamp : BitVec 64
  stock : Alpha 8
  buySideRpiExchanges : BitVec 8
  sellSideRpiExchanges : BitVec 8
  deriving DecidableEq, Repr

namespace RetailPriceImprovementMessage

def encode (message : RetailPriceImprovementMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 1 message.buySideRpiExchanges
    ++ (encodeUInt 1 message.sellSideRpiExchanges)))

def decode (bytes : List UInt8) : Option (RetailPriceImprovementMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (buySideRpiExchanges, bytes) ← decodeUInt 1 bytes
  let (sellSideRpiExchanges, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, stock, buySideRpiExchanges, sellSideRpiExchanges }, bytes)

@[simp] theorem encode_length (message : RetailPriceImprovementMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RetailPriceImprovementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetailPriceImprovementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RetailPriceImprovementMessage

/-- Trading Action Message: 21 bytes -/
structure TradingActionMessage where
  timestamp : BitVec 64
  stock : Alpha 8
  tradingState : TradingState
  reasonCode : Alpha 4
  deriving DecidableEq, Repr

namespace TradingActionMessage

def encode (message : TradingActionMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (TradingState.encode message.tradingState
    ++ (Alpha.encode message.reasonCode)))

def decode (bytes : List UInt8) : Option (TradingActionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  let (reasonCode, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, stock, tradingState, reasonCode }, bytes)

@[simp] theorem encode_length (message : TradingActionMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradingState.encode_length]

theorem encode_length_pos (message : TradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingState.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradingActionMessage

/-- Reg Sho Restriction Message: 17 bytes -/
structure RegShoRestrictionMessage where
  timestamp : BitVec 64
  stock : Alpha 8
  regShoAction : RegShoAction
  deriving DecidableEq, Repr

namespace RegShoRestrictionMessage

def encode (message : RegShoRestrictionMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (RegShoAction.encode message.regShoAction))

def decode (bytes : List UInt8) : Option (RegShoRestrictionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (regShoAction, bytes) ← RegShoAction.decode bytes
  pure ({ timestamp, stock, regShoAction }, bytes)

@[simp] theorem encode_length (message : RegShoRestrictionMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, RegShoAction.encode_length]

theorem encode_length_pos (message : RegShoRestrictionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegShoRestrictionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RegShoAction.decode_encode, some_bind]
  rfl

end RegShoRestrictionMessage

/-- Stock Directory Message: 36 bytes -/
structure StockDirectoryMessage where
  timestamp : BitVec 64
  stock : Alpha 8
  marketCategory : MarketCategory
  financialStatusIndicator : FinancialStatusIndicator
  roundLotSize : BitVec 32
  roundLotsOnly : RoundLotsOnly
  issueClassification : IssueClassification
  issueSubType : Alpha 2
  authenticity : Authenticity
  shortSaleThresholdIndicator : ShortSaleThresholdIndicator
  ipoFlag : IpoFlag
  luldReferencePriceTier : LuldReferencePriceTier
  etpFlag : EtpFlag
  etpLeverageFactor : BitVec 32
  inverseIndicator : InverseIndicator
  deriving DecidableEq, Repr

namespace StockDirectoryMessage

def encode (message : StockDirectoryMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (MarketCategory.encode message.marketCategory
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (encodeUInt 4 message.roundLotSize
    ++ (RoundLotsOnly.encode message.roundLotsOnly
    ++ (IssueClassification.encode message.issueClassification
    ++ (Alpha.encode message.issueSubType
    ++ (Authenticity.encode message.authenticity
    ++ (ShortSaleThresholdIndicator.encode message.shortSaleThresholdIndicator
    ++ (IpoFlag.encode message.ipoFlag
    ++ (LuldReferencePriceTier.encode message.luldReferencePriceTier
    ++ (EtpFlag.encode message.etpFlag
    ++ (encodeUInt 4 message.etpLeverageFactor
    ++ (InverseIndicator.encode message.inverseIndicator))))))))))))))

def decode (bytes : List UInt8) : Option (StockDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (marketCategory, bytes) ← MarketCategory.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (roundLotsOnly, bytes) ← RoundLotsOnly.decode bytes
  let (issueClassification, bytes) ← IssueClassification.decode bytes
  let (issueSubType, bytes) ← Alpha.decode 2 bytes
  let (authenticity, bytes) ← Authenticity.decode bytes
  let (shortSaleThresholdIndicator, bytes) ← ShortSaleThresholdIndicator.decode bytes
  let (ipoFlag, bytes) ← IpoFlag.decode bytes
  let (luldReferencePriceTier, bytes) ← LuldReferencePriceTier.decode bytes
  let (etpFlag, bytes) ← EtpFlag.decode bytes
  let (etpLeverageFactor, bytes) ← decodeUInt 4 bytes
  let (inverseIndicator, bytes) ← InverseIndicator.decode bytes
  pure ({ timestamp, stock, marketCategory, financialStatusIndicator, roundLotSize, roundLotsOnly, issueClassification, issueSubType, authenticity, shortSaleThresholdIndicator, ipoFlag, luldReferencePriceTier, etpFlag, etpLeverageFactor, inverseIndicator }, bytes)

@[simp] theorem encode_length (message : StockDirectoryMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, MarketCategory.encode_length, FinancialStatusIndicator.encode_length, RoundLotsOnly.encode_length, IssueClassification.encode_length, Authenticity.encode_length, ShortSaleThresholdIndicator.encode_length, IpoFlag.encode_length, LuldReferencePriceTier.encode_length, EtpFlag.encode_length, InverseIndicator.encode_length]

theorem encode_length_pos (message : StockDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialStatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RoundLotsOnly.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IssueClassification.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Authenticity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleThresholdIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IpoFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LuldReferencePriceTier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EtpFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [InverseIndicator.decode_encode, some_bind]
  rfl

end StockDirectoryMessage

/-- Mwcb Decline Level Message: 32 bytes -/
structure MwcbDeclineLevelMessage where
  timestamp : BitVec 64
  level1 : BitVec 64
  level2 : BitVec 64
  level3 : BitVec 64
  deriving DecidableEq, Repr

namespace MwcbDeclineLevelMessage

def encode (message : MwcbDeclineLevelMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 8 message.level1
    ++ (encodeUInt 8 message.level2
    ++ (encodeUInt 8 message.level3)))

def decode (bytes : List UInt8) : Option (MwcbDeclineLevelMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (level1, bytes) ← decodeUInt 8 bytes
  let (level2, bytes) ← decodeUInt 8 bytes
  let (level3, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, level1, level2, level3 }, bytes)

@[simp] theorem encode_length (message : MwcbDeclineLevelMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : MwcbDeclineLevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MwcbDeclineLevelMessage) (rest : List UInt8) :
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

end MwcbDeclineLevelMessage

/-- Mwcb Status Message: 9 bytes -/
structure MwcbStatusMessage where
  timestamp : BitVec 64
  breachedLevel : BreachedLevel
  deriving DecidableEq, Repr

namespace MwcbStatusMessage

def encode (message : MwcbStatusMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (BreachedLevel.encode message.breachedLevel)

def decode (bytes : List UInt8) : Option (MwcbStatusMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (breachedLevel, bytes) ← BreachedLevel.decode bytes
  pure ({ timestamp, breachedLevel }, bytes)

@[simp] theorem encode_length (message : MwcbStatusMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BreachedLevel.encode_length]

theorem encode_length_pos (message : MwcbStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MwcbStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [BreachedLevel.decode_encode, some_bind]
  rfl

end MwcbStatusMessage

/-- Ipo Quoting Period Update: 29 bytes -/
structure IpoQuotingPeriodUpdate where
  timestamp : BitVec 64
  stock : Alpha 8
  ipoQuotationReleaseTime : BitVec 32
  ipoQuotationReleaseQualifier : IpoQuotationReleaseQualifier
  ipoPrice : BitVec 64
  deriving DecidableEq, Repr

namespace IpoQuotingPeriodUpdate

def encode (message : IpoQuotingPeriodUpdate) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 4 message.ipoQuotationReleaseTime
    ++ (IpoQuotationReleaseQualifier.encode message.ipoQuotationReleaseQualifier
    ++ (encodeUInt 8 message.ipoPrice))))

def decode (bytes : List UInt8) : Option (IpoQuotingPeriodUpdate × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (ipoQuotationReleaseTime, bytes) ← decodeUInt 4 bytes
  let (ipoQuotationReleaseQualifier, bytes) ← IpoQuotationReleaseQualifier.decode bytes
  let (ipoPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, stock, ipoQuotationReleaseTime, ipoQuotationReleaseQualifier, ipoPrice }, bytes)

@[simp] theorem encode_length (message : IpoQuotingPeriodUpdate) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, IpoQuotationReleaseQualifier.encode_length]

theorem encode_length_pos (message : IpoQuotingPeriodUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IpoQuotingPeriodUpdate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, IpoQuotationReleaseQualifier.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IpoQuotingPeriodUpdate

/-- Operational Halt Message: 18 bytes -/
structure OperationalHaltMessage where
  timestamp : BitVec 64
  stock : Alpha 8
  marketCode : MarketCode
  operationalHaltAction : OperationalHaltAction
  deriving DecidableEq, Repr

namespace OperationalHaltMessage

def encode (message : OperationalHaltMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (MarketCode.encode message.marketCode
    ++ (OperationalHaltAction.encode message.operationalHaltAction)))

def decode (bytes : List UInt8) : Option (OperationalHaltMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (marketCode, bytes) ← MarketCode.decode bytes
  let (operationalHaltAction, bytes) ← OperationalHaltAction.decode bytes
  pure ({ timestamp, stock, marketCode, operationalHaltAction }, bytes)

@[simp] theorem encode_length (message : OperationalHaltMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, MarketCode.encode_length, OperationalHaltAction.encode_length]

theorem encode_length_pos (message : OperationalHaltMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OperationalHaltMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCode.decode_encode, some_bind]
  dsimp only
  rw [OperationalHaltAction.decode_encode, some_bind]
  rfl

end OperationalHaltMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | consolidatedQuotationMessage (message : ConsolidatedQuotationMessage) -- "Q" 0x51
  | retailPriceImprovementMessage (message : RetailPriceImprovementMessage) -- "N" 0x4E
  | tradingActionMessage (message : TradingActionMessage) -- "H" 0x48
  | regShoRestrictionMessage (message : RegShoRestrictionMessage) -- "Y" 0x59
  | stockDirectoryMessage (message : StockDirectoryMessage) -- "R" 0x52
  | mwcbDeclineLevelMessage (message : MwcbDeclineLevelMessage) -- "V" 0x56
  | mwcbStatusMessage (message : MwcbStatusMessage) -- "W" 0x57
  | ipoQuotingPeriodUpdate (message : IpoQuotingPeriodUpdate) -- "K" 0x4B
  | operationalHaltMessage (message : OperationalHaltMessage) -- "h" 0x68
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .consolidatedQuotationMessage _ => 81
  | .retailPriceImprovementMessage _ => 78
  | .tradingActionMessage _ => 72
  | .regShoRestrictionMessage _ => 89
  | .stockDirectoryMessage _ => 82
  | .mwcbDeclineLevelMessage _ => 86
  | .mwcbStatusMessage _ => 87
  | .ipoQuotingPeriodUpdate _ => 75
  | .operationalHaltMessage _ => 104

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .consolidatedQuotationMessage message => ConsolidatedQuotationMessage.encode message
  | .retailPriceImprovementMessage message => RetailPriceImprovementMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .regShoRestrictionMessage message => RegShoRestrictionMessage.encode message
  | .stockDirectoryMessage message => StockDirectoryMessage.encode message
  | .mwcbDeclineLevelMessage message => MwcbDeclineLevelMessage.encode message
  | .mwcbStatusMessage message => MwcbStatusMessage.encode message
  | .ipoQuotingPeriodUpdate message => IpoQuotingPeriodUpdate.encode message
  | .operationalHaltMessage message => OperationalHaltMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 42 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | consolidatedQuotationMessage inner =>
    simp only [encode, ConsolidatedQuotationMessage.encode_length]
    omega
  | retailPriceImprovementMessage inner =>
    simp only [encode, RetailPriceImprovementMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [encode, TradingActionMessage.encode_length]
    omega
  | regShoRestrictionMessage inner =>
    simp only [encode, RegShoRestrictionMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [encode, StockDirectoryMessage.encode_length]
    omega
  | mwcbDeclineLevelMessage inner =>
    simp only [encode, MwcbDeclineLevelMessage.encode_length]
    omega
  | mwcbStatusMessage inner =>
    simp only [encode, MwcbStatusMessage.encode_length]
    omega
  | ipoQuotingPeriodUpdate inner =>
    simp only [encode, IpoQuotingPeriodUpdate.encode_length]
    omega
  | operationalHaltMessage inner =>
    simp only [encode, OperationalHaltMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 81 then (ConsolidatedQuotationMessage.decode bytes).map fun (message, rest) => (.consolidatedQuotationMessage message, rest)
  else if tag = 78 then (RetailPriceImprovementMessage.decode bytes).map fun (message, rest) => (.retailPriceImprovementMessage message, rest)
  else if tag = 72 then (TradingActionMessage.decode bytes).map fun (message, rest) => (.tradingActionMessage message, rest)
  else if tag = 89 then (RegShoRestrictionMessage.decode bytes).map fun (message, rest) => (.regShoRestrictionMessage message, rest)
  else if tag = 82 then (StockDirectoryMessage.decode bytes).map fun (message, rest) => (.stockDirectoryMessage message, rest)
  else if tag = 86 then (MwcbDeclineLevelMessage.decode bytes).map fun (message, rest) => (.mwcbDeclineLevelMessage message, rest)
  else if tag = 87 then (MwcbStatusMessage.decode bytes).map fun (message, rest) => (.mwcbStatusMessage message, rest)
  else if tag = 75 then (IpoQuotingPeriodUpdate.decode bytes).map fun (message, rest) => (.ipoQuotingPeriodUpdate message, rest)
  else if tag = 104 then (OperationalHaltMessage.decode bytes).map fun (message, rest) => (.operationalHaltMessage message, rest)
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
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | consolidatedQuotationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ConsolidatedQuotationMessage.encode_length]
    omega
  | retailPriceImprovementMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RetailPriceImprovementMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingActionMessage.encode_length]
    omega
  | regShoRestrictionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RegShoRestrictionMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockDirectoryMessage.encode_length]
    omega
  | mwcbDeclineLevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MwcbDeclineLevelMessage.encode_length]
    omega
  | mwcbStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MwcbStatusMessage.encode_length]
    omega
  | ipoQuotingPeriodUpdate inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IpoQuotingPeriodUpdate.encode_length]
    omega
  | operationalHaltMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OperationalHaltMessage.encode_length]
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

end Omi.NasdaqNsmequitiesBasicplusItchV10
