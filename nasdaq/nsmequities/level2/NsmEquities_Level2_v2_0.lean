import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Level 2 v2.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesLevel2ItchV20

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

/-- Market Category: one byte code -/
def MarketCategory.codes : List UInt8 :=
  [0x51, 0x47, 0x53, 0x4E, 0x41, 0x50, 0x4D, 0x5A, 0x56, 0x20]

inductive MarketCategory where
  | nasdaqGlobalSelectMarket -- Nasdaq Global Select Market
  | nasdaqGlobalMarket -- Nasdaq Global Market
  | nasdaqCapitalMarket -- Nasdaq Capital Market
  | newYorkStockExchange -- New York Stock Exchange
  | nyseAmerican -- Nyse American
  | nyseArca -- Nyse Arca
  | nyseTexas -- Nyse Texas
  | batsBzxExchange -- Bats Bzx Exchange
  | investorsExchangeLlc -- Investors Exchange Llc
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCategory

def toByte : MarketCategory → UInt8
  | .nasdaqGlobalSelectMarket => 0x51
  | .nasdaqGlobalMarket => 0x47
  | .nasdaqCapitalMarket => 0x53
  | .newYorkStockExchange => 0x4E
  | .nyseAmerican => 0x41
  | .nyseArca => 0x50
  | .nyseTexas => 0x4D
  | .batsBzxExchange => 0x5A
  | .investorsExchangeLlc => 0x56
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCategory :=
  if byte = 0x51 then .nasdaqGlobalSelectMarket
  else if byte = 0x47 then .nasdaqGlobalMarket
  else if byte = 0x53 then .nasdaqCapitalMarket
  else if byte = 0x4E then .newYorkStockExchange
  else if byte = 0x41 then .nyseAmerican
  else if byte = 0x50 then .nyseArca
  else if byte = 0x4D then .nyseTexas
  else if byte = 0x5A then .batsBzxExchange
  else if byte = 0x56 then .investorsExchangeLlc
  else .notAvailable

def ofByte (byte : UInt8) : MarketCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCategory) : ofByte value.toByte = value := by
  cases value with
  | nasdaqGlobalSelectMarket => decide
  | nasdaqGlobalMarket => decide
  | nasdaqCapitalMarket => decide
  | newYorkStockExchange => decide
  | nyseAmerican => decide
  | nyseArca => decide
  | nyseTexas => decide
  | batsBzxExchange => decide
  | investorsExchangeLlc => decide
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
  | creationsAndorRedemptionsSuspendedForExchangeTradedProduct -- Creations Andor Redemptions Suspended For Exchange Traded Product
  | normal -- Normal
  | inCompliance -- In Compliance
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
  | .creationsAndorRedemptionsSuspendedForExchangeTradedProduct => 0x43
  | .normal => 0x4E
  | .inCompliance => 0x20
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
  else if byte = 0x43 then .creationsAndorRedemptionsSuspendedForExchangeTradedProduct
  else if byte = 0x4E then .normal
  else .inCompliance

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
  | creationsAndorRedemptionsSuspendedForExchangeTradedProduct => decide
  | normal => decide
  | inCompliance => decide
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
  | roundLotsOnly -- Round Lots Only
  | noRestriction -- No Restriction
  | unlisted (byte : { byte : UInt8 // byte ∉ RoundLotsOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RoundLotsOnly

def toByte : RoundLotsOnly → UInt8
  | .roundLotsOnly => 0x59
  | .noRestriction => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RoundLotsOnly :=
  if byte = 0x59 then .roundLotsOnly
  else .noRestriction

def ofByte (byte : UInt8) : RoundLotsOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RoundLotsOnly) : ofByte value.toByte = value := by
  cases value with
  | roundLotsOnly => decide
  | noRestriction => decide
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
  | unitsBenifInt -- Units Benif Int
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
  | .unitsBenifInt => 0x56
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
  else if byte = 0x56 then .unitsBenifInt
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
  | unitsBenifInt => decide
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
  | ipoSecurity -- Ipo Security
  | notIpo -- Not Ipo
  | nonIpoNewListed -- Non Ipo New Listed
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ IpoFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IpoFlag

def toByte : IpoFlag → UInt8
  | .ipoSecurity => 0x59
  | .notIpo => 0x4E
  | .nonIpoNewListed => 0x5A
  | .notAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IpoFlag :=
  if byte = 0x59 then .ipoSecurity
  else if byte = 0x4E then .notIpo
  else if byte = 0x5A then .nonIpoNewListed
  else .notAvailable

def ofByte (byte : UInt8) : IpoFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IpoFlag) : ofByte value.toByte = value := by
  cases value with
  | ipoSecurity => decide
  | notIpo => decide
  | nonIpoNewListed => decide
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
  | inverse -- Inverse
  | notInverse -- Not Inverse
  | unlisted (byte : { byte : UInt8 // byte ∉ InverseIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InverseIndicator

def toByte : InverseIndicator → UInt8
  | .inverse => 0x59
  | .notInverse => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InverseIndicator :=
  if byte = 0x59 then .inverse
  else .notInverse

def ofByte (byte : UInt8) : InverseIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InverseIndicator) : ofByte value.toByte = value := by
  cases value with
  | inverse => decide
  | notInverse => decide
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

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x48, 0x50, 0x51, 0x54]

inductive CurrentTradingState where
  | halted -- Halted
  | paused -- Paused
  | quotationOnly -- Quotation Only
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .halted => 0x48
  | .paused => 0x50
  | .quotationOnly => 0x51
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .halted
  else if byte = 0x50 then .paused
  else if byte = 0x51 then .quotationOnly
  else .trading

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | paused => decide
  | quotationOnly => decide
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

/-- Reg Sho Action: one byte code -/
def RegShoAction.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive RegShoAction where
  | noPriceTest -- No Price Test
  | restrictionInEffect -- Restriction In Effect
  | restrictionRemainsInEffect -- Restriction Remains In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ RegShoAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RegShoAction

def toByte : RegShoAction → UInt8
  | .noPriceTest => 0x30
  | .restrictionInEffect => 0x31
  | .restrictionRemainsInEffect => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RegShoAction :=
  if byte = 0x30 then .noPriceTest
  else if byte = 0x31 then .restrictionInEffect
  else .restrictionRemainsInEffect

def ofByte (byte : UInt8) : RegShoAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RegShoAction) : ofByte value.toByte = value := by
  cases value with
  | noPriceTest => decide
  | restrictionInEffect => decide
  | restrictionRemainsInEffect => decide
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

/-- Primary Market Maker: one byte code -/
def PrimaryMarketMaker.codes : List UInt8 :=
  [0x59, 0x4E]

inductive PrimaryMarketMaker where
  | primaryMarketMaker -- Primary Market Maker
  | nonPrimaryMarketMaker -- Non Primary Market Maker
  | unlisted (byte : { byte : UInt8 // byte ∉ PrimaryMarketMaker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrimaryMarketMaker

def toByte : PrimaryMarketMaker → UInt8
  | .primaryMarketMaker => 0x59
  | .nonPrimaryMarketMaker => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrimaryMarketMaker :=
  if byte = 0x59 then .primaryMarketMaker
  else .nonPrimaryMarketMaker

def ofByte (byte : UInt8) : PrimaryMarketMaker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrimaryMarketMaker) : ofByte value.toByte = value := by
  cases value with
  | primaryMarketMaker => decide
  | nonPrimaryMarketMaker => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrimaryMarketMaker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrimaryMarketMaker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrimaryMarketMaker) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrimaryMarketMaker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrimaryMarketMaker

/-- Market Maker Mode: one byte code -/
def MarketMakerMode.codes : List UInt8 :=
  [0x4E, 0x50, 0x53, 0x52, 0x4C]

inductive MarketMakerMode where
  | normal -- Normal
  | passive -- Passive
  | syndicate -- Syndicate
  | preSyndicate -- Pre Syndicate
  | penalty -- Penalty
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketMakerMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketMakerMode

def toByte : MarketMakerMode → UInt8
  | .normal => 0x4E
  | .passive => 0x50
  | .syndicate => 0x53
  | .preSyndicate => 0x52
  | .penalty => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketMakerMode :=
  if byte = 0x4E then .normal
  else if byte = 0x50 then .passive
  else if byte = 0x53 then .syndicate
  else if byte = 0x52 then .preSyndicate
  else .penalty

def ofByte (byte : UInt8) : MarketMakerMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketMakerMode) : ofByte value.toByte = value := by
  cases value with
  | normal => decide
  | passive => decide
  | syndicate => decide
  | preSyndicate => decide
  | penalty => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketMakerMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketMakerMode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketMakerMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketMakerMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketMakerMode

/-- Market Participant State: one byte code -/
def MarketParticipantState.codes : List UInt8 :=
  [0x41, 0x45, 0x57, 0x53, 0x44]

inductive MarketParticipantState where
  | active -- Active
  | excusedWithdrawn -- Excused Withdrawn
  | withdrawn -- Withdrawn
  | suspended -- Suspended
  | deleted -- Deleted
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketParticipantState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketParticipantState

def toByte : MarketParticipantState → UInt8
  | .active => 0x41
  | .excusedWithdrawn => 0x45
  | .withdrawn => 0x57
  | .suspended => 0x53
  | .deleted => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketParticipantState :=
  if byte = 0x41 then .active
  else if byte = 0x45 then .excusedWithdrawn
  else if byte = 0x57 then .withdrawn
  else if byte = 0x53 then .suspended
  else .deleted

def ofByte (byte : UInt8) : MarketParticipantState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketParticipantState) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | excusedWithdrawn => decide
  | withdrawn => decide
  | suspended => decide
  | deleted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketParticipantState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketParticipantState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketParticipantState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketParticipantState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketParticipantState

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
  | operationallyHalted -- Operationally Halted
  | tradingResumed -- Trading Resumed
  | unlisted (byte : { byte : UInt8 // byte ∉ OperationalHaltAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OperationalHaltAction

def toByte : OperationalHaltAction → UInt8
  | .operationallyHalted => 0x48
  | .tradingResumed => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OperationalHaltAction :=
  if byte = 0x48 then .operationallyHalted
  else .tradingResumed

def ofByte (byte : UInt8) : OperationalHaltAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OperationalHaltAction) : ofByte value.toByte = value := by
  cases value with
  | operationallyHalted => decide
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

/-- Market Side: one byte code -/
def MarketSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive MarketSide where
  | bidUpdate -- Bid Update
  | offerAskUpdate -- Offer Ask Update
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketSide

def toByte : MarketSide → UInt8
  | .bidUpdate => 0x42
  | .offerAskUpdate => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketSide :=
  if byte = 0x42 then .bidUpdate
  else .offerAskUpdate

def ofByte (byte : UInt8) : MarketSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketSide) : ofByte value.toByte = value := by
  cases value with
  | bidUpdate => decide
  | offerAskUpdate => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketSide

/-- Interest Flag: one byte code -/
def InterestFlag.codes : List UInt8 :=
  [0x42, 0x53, 0x41, 0x4E]

inductive InterestFlag where
  | buySide -- Buy Side
  | sellSide -- Sell Side
  | bothSides -- Both Sides
  | noRpiOrders -- No Rpi Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ InterestFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InterestFlag

def toByte : InterestFlag → UInt8
  | .buySide => 0x42
  | .sellSide => 0x53
  | .bothSides => 0x41
  | .noRpiOrders => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InterestFlag :=
  if byte = 0x42 then .buySide
  else if byte = 0x53 then .sellSide
  else if byte = 0x41 then .bothSides
  else .noRpiOrders

def ofByte (byte : UInt8) : InterestFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InterestFlag) : ofByte value.toByte = value := by
  cases value with
  | buySide => decide
  | sellSide => decide
  | bothSides => decide
  | noRpiOrders => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InterestFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InterestFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InterestFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InterestFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InterestFlag

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
  | ipoReleaseCanceledPostponed -- Ipo Release Canceled Postponed
  | unlisted (byte : { byte : UInt8 // byte ∉ IpoQuotationReleaseQualifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IpoQuotationReleaseQualifier

def toByte : IpoQuotationReleaseQualifier → UInt8
  | .anticipatedQuotationReleaseTime => 0x41
  | .ipoReleaseCanceledPostponed => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IpoQuotationReleaseQualifier :=
  if byte = 0x41 then .anticipatedQuotationReleaseTime
  else .ipoReleaseCanceledPostponed

def ofByte (byte : UInt8) : IpoQuotationReleaseQualifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IpoQuotationReleaseQualifier) : ofByte value.toByte = value := by
  cases value with
  | anticipatedQuotationReleaseTime => decide
  | ipoReleaseCanceledPostponed => decide
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

/-- System Event Message: 9 bytes -/
structure SystemEventMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (EventCode.encode message.eventCode))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ trackingNumber, timestamp, eventCode }, bytes)

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Stock Directory Message: 36 bytes -/
structure StockDirectoryMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  stock : Alpha 8
  marketCategory : MarketCategory
  financialStatusIndicator : FinancialStatusIndicator
  roundLotSize : BitVec 32
  roundLotsOnly : RoundLotsOnly
  issueClassification : IssueClassification
  issueSubtype : Alpha 2
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
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (MarketCategory.encode message.marketCategory
    ++ (FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ (encodeUInt 4 message.roundLotSize
    ++ (RoundLotsOnly.encode message.roundLotsOnly
    ++ (IssueClassification.encode message.issueClassification
    ++ (Alpha.encode message.issueSubtype
    ++ (Authenticity.encode message.authenticity
    ++ (ShortSaleThresholdIndicator.encode message.shortSaleThresholdIndicator
    ++ (IpoFlag.encode message.ipoFlag
    ++ (LuldReferencePriceTier.encode message.luldReferencePriceTier
    ++ (EtpFlag.encode message.etpFlag
    ++ (encodeUInt 4 message.etpLeverageFactor
    ++ (InverseIndicator.encode message.inverseIndicator)))))))))))))))

def decode (bytes : List UInt8) : Option (StockDirectoryMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (marketCategory, bytes) ← MarketCategory.decode bytes
  let (financialStatusIndicator, bytes) ← FinancialStatusIndicator.decode bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (roundLotsOnly_, bytes) ← RoundLotsOnly.decode bytes
  let (issueClassification, bytes) ← IssueClassification.decode bytes
  let (issueSubtype, bytes) ← Alpha.decode 2 bytes
  let (authenticity, bytes) ← Authenticity.decode bytes
  let (shortSaleThresholdIndicator, bytes) ← ShortSaleThresholdIndicator.decode bytes
  let (ipoFlag, bytes) ← IpoFlag.decode bytes
  let (luldReferencePriceTier, bytes) ← LuldReferencePriceTier.decode bytes
  let (etpFlag, bytes) ← EtpFlag.decode bytes
  let (etpLeverageFactor, bytes) ← decodeUInt 4 bytes
  let (inverseIndicator, bytes) ← InverseIndicator.decode bytes
  pure ({ trackingNumber, timestamp, stock, marketCategory, financialStatusIndicator, roundLotSize, roundLotsOnly := roundLotsOnly_, issueClassification, issueSubtype, authenticity, shortSaleThresholdIndicator, ipoFlag, luldReferencePriceTier, etpFlag, etpLeverageFactor, inverseIndicator }, bytes)

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

/-- Stock Trading Action Message: 21 bytes -/
structure StockTradingActionMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  stock : Alpha 8
  currentTradingState : CurrentTradingState
  reason : Alpha 4
  deriving DecidableEq, Repr

namespace StockTradingActionMessage

def encode (message : StockTradingActionMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (CurrentTradingState.encode message.currentTradingState
    ++ (Alpha.encode message.reason))))

def decode (bytes : List UInt8) : Option (StockTradingActionMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  let (reason, bytes) ← Alpha.decode 4 bytes
  pure ({ trackingNumber, timestamp, stock, currentTradingState, reason }, bytes)

@[simp] theorem encode_length (message : StockTradingActionMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : StockTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CurrentTradingState.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockTradingActionMessage

/-- Reg Sho Short Sale Price Test Restricted Indicator Message: 17 bytes -/
structure RegShoShortSalePriceTestRestrictedIndicatorMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  stock : Alpha 8
  regShoAction : RegShoAction
  deriving DecidableEq, Repr

namespace RegShoShortSalePriceTestRestrictedIndicatorMessage

def encode (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (RegShoAction.encode message.regShoAction)))

def decode (bytes : List UInt8) : Option (RegShoShortSalePriceTestRestrictedIndicatorMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (regShoAction, bytes) ← RegShoAction.decode bytes
  pure ({ trackingNumber, timestamp, stock, regShoAction }, bytes)

@[simp] theorem encode_length (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, RegShoAction.encode_length]

theorem encode_length_pos (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RegShoAction.decode_encode, some_bind]
  rfl

end RegShoShortSalePriceTestRestrictedIndicatorMessage

/-- Market Participant Position Message: 23 bytes -/
structure MarketParticipantPositionMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  mpid : Alpha 4
  stock : Alpha 8
  primaryMarketMaker : PrimaryMarketMaker
  marketMakerMode : MarketMakerMode
  marketParticipantState : MarketParticipantState
  deriving DecidableEq, Repr

namespace MarketParticipantPositionMessage

def encode (message : MarketParticipantPositionMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.stock
    ++ (PrimaryMarketMaker.encode message.primaryMarketMaker
    ++ (MarketMakerMode.encode message.marketMakerMode
    ++ (MarketParticipantState.encode message.marketParticipantState))))))

def decode (bytes : List UInt8) : Option (MarketParticipantPositionMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (primaryMarketMaker_, bytes) ← PrimaryMarketMaker.decode bytes
  let (marketMakerMode, bytes) ← MarketMakerMode.decode bytes
  let (marketParticipantState, bytes) ← MarketParticipantState.decode bytes
  pure ({ trackingNumber, timestamp, mpid, stock, primaryMarketMaker := primaryMarketMaker_, marketMakerMode, marketParticipantState }, bytes)

@[simp] theorem encode_length (message : MarketParticipantPositionMessage) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, PrimaryMarketMaker.encode_length, MarketMakerMode.encode_length, MarketParticipantState.encode_length]

theorem encode_length_pos (message : MarketParticipantPositionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketParticipantPositionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, PrimaryMarketMaker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMakerMode.decode_encode, some_bind]
  dsimp only
  rw [MarketParticipantState.decode_encode, some_bind]
  rfl

end MarketParticipantPositionMessage

/-- Operational Halt Message: 18 bytes -/
structure OperationalHaltMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  stock : Alpha 8
  marketCode : MarketCode
  operationalHaltAction : OperationalHaltAction
  deriving DecidableEq, Repr

namespace OperationalHaltMessage

def encode (message : OperationalHaltMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (MarketCode.encode message.marketCode
    ++ (OperationalHaltAction.encode message.operationalHaltAction))))

def decode (bytes : List UInt8) : Option (OperationalHaltMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (marketCode, bytes) ← MarketCode.decode bytes
  let (operationalHaltAction, bytes) ← OperationalHaltAction.decode bytes
  pure ({ trackingNumber, timestamp, stock, marketCode, operationalHaltAction }, bytes)

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCode.decode_encode, some_bind]
  dsimp only
  rw [OperationalHaltAction.decode_encode, some_bind]
  rfl

end OperationalHaltMessage

/-- Market Participant Bid Ask Update Message: 29 bytes -/
structure MarketParticipantBidAskUpdateMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  marketSide : MarketSide
  participantShares : BitVec 32
  stock : Alpha 8
  price : BitVec 32
  mpid : Alpha 4
  deriving DecidableEq, Repr

namespace MarketParticipantBidAskUpdateMessage

def encode (message : MarketParticipantBidAskUpdateMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (MarketSide.encode message.marketSide
    ++ (encodeUInt 4 message.participantShares
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 4 message.price
    ++ (Alpha.encode message.mpid))))))

def decode (bytes : List UInt8) : Option (MarketParticipantBidAskUpdateMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (marketSide, bytes) ← MarketSide.decode bytes
  let (participantShares, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  pure ({ trackingNumber, timestamp, marketSide, participantShares, stock, price, mpid }, bytes)

@[simp] theorem encode_length (message : MarketParticipantBidAskUpdateMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, MarketSide.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketParticipantBidAskUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketParticipantBidAskUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MarketSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketParticipantBidAskUpdateMessage

/-- Retail Price Interest Indicator Message: 17 bytes -/
structure RetailPriceInterestIndicatorMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  stock : Alpha 8
  interestFlag : InterestFlag
  deriving DecidableEq, Repr

namespace RetailPriceInterestIndicatorMessage

def encode (message : RetailPriceInterestIndicatorMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (InterestFlag.encode message.interestFlag)))

def decode (bytes : List UInt8) : Option (RetailPriceInterestIndicatorMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (interestFlag, bytes) ← InterestFlag.decode bytes
  pure ({ trackingNumber, timestamp, stock, interestFlag }, bytes)

@[simp] theorem encode_length (message : RetailPriceInterestIndicatorMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, InterestFlag.encode_length]

theorem encode_length_pos (message : RetailPriceInterestIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetailPriceInterestIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InterestFlag.decode_encode, some_bind]
  rfl

end RetailPriceInterestIndicatorMessage

/-- Market Wide Circuit Breaker Decline Level Message: 32 bytes -/
structure MarketWideCircuitBreakerDeclineLevelMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  level1 : BitVec 64
  level2 : BitVec 64
  level3 : BitVec 64
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerDeclineLevelMessage

def encode (message : MarketWideCircuitBreakerDeclineLevelMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (encodeUInt 8 message.level1
    ++ (encodeUInt 8 message.level2
    ++ (encodeUInt 8 message.level3))))

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerDeclineLevelMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (level1, bytes) ← decodeUInt 8 bytes
  let (level2, bytes) ← decodeUInt 8 bytes
  let (level3, bytes) ← decodeUInt 8 bytes
  pure ({ trackingNumber, timestamp, level1, level2, level3 }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerDeclineLevelMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : MarketWideCircuitBreakerDeclineLevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketWideCircuitBreakerDeclineLevelMessage) (rest : List UInt8) :
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

end MarketWideCircuitBreakerDeclineLevelMessage

/-- Market Wide Circuit Breaker Status Message: 9 bytes -/
structure MarketWideCircuitBreakerStatusMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  breachedLevel : BreachedLevel
  deriving DecidableEq, Repr

namespace MarketWideCircuitBreakerStatusMessage

def encode (message : MarketWideCircuitBreakerStatusMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (BreachedLevel.encode message.breachedLevel))

def decode (bytes : List UInt8) : Option (MarketWideCircuitBreakerStatusMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (breachedLevel, bytes) ← BreachedLevel.decode bytes
  pure ({ trackingNumber, timestamp, breachedLevel }, bytes)

@[simp] theorem encode_length (message : MarketWideCircuitBreakerStatusMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BreachedLevel.encode_length]

theorem encode_length_pos (message : MarketWideCircuitBreakerStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketWideCircuitBreakerStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [BreachedLevel.decode_encode, some_bind]
  rfl

end MarketWideCircuitBreakerStatusMessage

/-- Ipo Quoting Period Update Message: 25 bytes -/
structure IpoQuotingPeriodUpdateMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  stock : Alpha 8
  ipoQuotationReleaseTime : BitVec 32
  ipoQuotationReleaseQualifier : IpoQuotationReleaseQualifier
  ipoPrice : BitVec 32
  deriving DecidableEq, Repr

namespace IpoQuotingPeriodUpdateMessage

def encode (message : IpoQuotingPeriodUpdateMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 6 message.timestamp
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 4 message.ipoQuotationReleaseTime
    ++ (IpoQuotationReleaseQualifier.encode message.ipoQuotationReleaseQualifier
    ++ (encodeUInt 4 message.ipoPrice)))))

def decode (bytes : List UInt8) : Option (IpoQuotingPeriodUpdateMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (ipoQuotationReleaseTime, bytes) ← decodeUInt 4 bytes
  let (ipoQuotationReleaseQualifier, bytes) ← IpoQuotationReleaseQualifier.decode bytes
  let (ipoPrice, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, stock, ipoQuotationReleaseTime, ipoQuotationReleaseQualifier, ipoPrice }, bytes)

@[simp] theorem encode_length (message : IpoQuotingPeriodUpdateMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, IpoQuotationReleaseQualifier.encode_length]

theorem encode_length_pos (message : IpoQuotingPeriodUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IpoQuotingPeriodUpdateMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, IpoQuotationReleaseQualifier.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IpoQuotingPeriodUpdateMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | stockDirectoryMessage (message : StockDirectoryMessage) -- "R" 0x52
  | stockTradingActionMessage (message : StockTradingActionMessage) -- "H" 0x48
  | regShoShortSalePriceTestRestrictedIndicatorMessage (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) -- "Y" 0x59
  | marketParticipantPositionMessage (message : MarketParticipantPositionMessage) -- "P" 0x50
  | operationalHaltMessage (message : OperationalHaltMessage) -- "h" 0x68
  | marketParticipantBidAskUpdateMessage (message : MarketParticipantBidAskUpdateMessage) -- "U" 0x55
  | retailPriceInterestIndicatorMessage (message : RetailPriceInterestIndicatorMessage) -- "N" 0x4E
  | marketWideCircuitBreakerDeclineLevelMessage (message : MarketWideCircuitBreakerDeclineLevelMessage) -- "V" 0x56
  | marketWideCircuitBreakerStatusMessage (message : MarketWideCircuitBreakerStatusMessage) -- "W" 0x57
  | ipoQuotingPeriodUpdateMessage (message : IpoQuotingPeriodUpdateMessage) -- "K" 0x4B
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .stockDirectoryMessage _ => 82
  | .stockTradingActionMessage _ => 72
  | .regShoShortSalePriceTestRestrictedIndicatorMessage _ => 89
  | .marketParticipantPositionMessage _ => 80
  | .operationalHaltMessage _ => 104
  | .marketParticipantBidAskUpdateMessage _ => 85
  | .retailPriceInterestIndicatorMessage _ => 78
  | .marketWideCircuitBreakerDeclineLevelMessage _ => 86
  | .marketWideCircuitBreakerStatusMessage _ => 87
  | .ipoQuotingPeriodUpdateMessage _ => 75

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .stockDirectoryMessage message => StockDirectoryMessage.encode message
  | .stockTradingActionMessage message => StockTradingActionMessage.encode message
  | .regShoShortSalePriceTestRestrictedIndicatorMessage message => RegShoShortSalePriceTestRestrictedIndicatorMessage.encode message
  | .marketParticipantPositionMessage message => MarketParticipantPositionMessage.encode message
  | .operationalHaltMessage message => OperationalHaltMessage.encode message
  | .marketParticipantBidAskUpdateMessage message => MarketParticipantBidAskUpdateMessage.encode message
  | .retailPriceInterestIndicatorMessage message => RetailPriceInterestIndicatorMessage.encode message
  | .marketWideCircuitBreakerDeclineLevelMessage message => MarketWideCircuitBreakerDeclineLevelMessage.encode message
  | .marketWideCircuitBreakerStatusMessage message => MarketWideCircuitBreakerStatusMessage.encode message
  | .ipoQuotingPeriodUpdateMessage message => IpoQuotingPeriodUpdateMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 36 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [encode, StockDirectoryMessage.encode_length]
    omega
  | stockTradingActionMessage inner =>
    simp only [encode, StockTradingActionMessage.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [encode, RegShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | marketParticipantPositionMessage inner =>
    simp only [encode, MarketParticipantPositionMessage.encode_length]
    omega
  | operationalHaltMessage inner =>
    simp only [encode, OperationalHaltMessage.encode_length]
    omega
  | marketParticipantBidAskUpdateMessage inner =>
    simp only [encode, MarketParticipantBidAskUpdateMessage.encode_length]
    omega
  | retailPriceInterestIndicatorMessage inner =>
    simp only [encode, RetailPriceInterestIndicatorMessage.encode_length]
    omega
  | marketWideCircuitBreakerDeclineLevelMessage inner =>
    simp only [encode, MarketWideCircuitBreakerDeclineLevelMessage.encode_length]
    omega
  | marketWideCircuitBreakerStatusMessage inner =>
    simp only [encode, MarketWideCircuitBreakerStatusMessage.encode_length]
    omega
  | ipoQuotingPeriodUpdateMessage inner =>
    simp only [encode, IpoQuotingPeriodUpdateMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (StockDirectoryMessage.decode bytes).map fun (message, rest) => (.stockDirectoryMessage message, rest)
  else if tag = 72 then (StockTradingActionMessage.decode bytes).map fun (message, rest) => (.stockTradingActionMessage message, rest)
  else if tag = 89 then (RegShoShortSalePriceTestRestrictedIndicatorMessage.decode bytes).map fun (message, rest) => (.regShoShortSalePriceTestRestrictedIndicatorMessage message, rest)
  else if tag = 80 then (MarketParticipantPositionMessage.decode bytes).map fun (message, rest) => (.marketParticipantPositionMessage message, rest)
  else if tag = 104 then (OperationalHaltMessage.decode bytes).map fun (message, rest) => (.operationalHaltMessage message, rest)
  else if tag = 85 then (MarketParticipantBidAskUpdateMessage.decode bytes).map fun (message, rest) => (.marketParticipantBidAskUpdateMessage message, rest)
  else if tag = 78 then (RetailPriceInterestIndicatorMessage.decode bytes).map fun (message, rest) => (.retailPriceInterestIndicatorMessage message, rest)
  else if tag = 86 then (MarketWideCircuitBreakerDeclineLevelMessage.decode bytes).map fun (message, rest) => (.marketWideCircuitBreakerDeclineLevelMessage message, rest)
  else if tag = 87 then (MarketWideCircuitBreakerStatusMessage.decode bytes).map fun (message, rest) => (.marketWideCircuitBreakerStatusMessage message, rest)
  else if tag = 75 then (IpoQuotingPeriodUpdateMessage.decode bytes).map fun (message, rest) => (.ipoQuotingPeriodUpdateMessage message, rest)
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
  | stockDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockDirectoryMessage.encode_length]
    omega
  | stockTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockTradingActionMessage.encode_length]
    omega
  | regShoShortSalePriceTestRestrictedIndicatorMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RegShoShortSalePriceTestRestrictedIndicatorMessage.encode_length]
    omega
  | marketParticipantPositionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketParticipantPositionMessage.encode_length]
    omega
  | operationalHaltMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OperationalHaltMessage.encode_length]
    omega
  | marketParticipantBidAskUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketParticipantBidAskUpdateMessage.encode_length]
    omega
  | retailPriceInterestIndicatorMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RetailPriceInterestIndicatorMessage.encode_length]
    omega
  | marketWideCircuitBreakerDeclineLevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketWideCircuitBreakerDeclineLevelMessage.encode_length]
    omega
  | marketWideCircuitBreakerStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketWideCircuitBreakerStatusMessage.encode_length]
    omega
  | ipoQuotingPeriodUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IpoQuotingPeriodUpdateMessage.encode_length]
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

end Omi.NasdaqNsmequitiesLevel2ItchV20
