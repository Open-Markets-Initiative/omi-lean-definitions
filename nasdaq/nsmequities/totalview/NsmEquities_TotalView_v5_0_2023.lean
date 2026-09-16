import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) TotalView Itch v5.0.2023

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesTotalviewItchV502023

/-- Event Code: one byte code -/
inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfMarketHours -- Start Of Market Hours
  | endOfMarketHours -- End Of Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfMarketHours => 0x51
  | .endOfMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43

def ofByte? (byte : UInt8) : Option EventCode :=
  if byte = 0x4F then some .startOfMessages
  else if byte = 0x53 then some .startOfSystemHours
  else if byte = 0x51 then some .startOfMarketHours
  else if byte = 0x4D then some .endOfMarketHours
  else if byte = 0x45 then some .endOfSystemHours
  else if byte = 0x43 then some .endOfMessages
  else none

theorem ofByte?_toByte (value : EventCode) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end EventCode

/-- Market Category: one byte code -/
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

def ofByte? (byte : UInt8) : Option MarketCategory :=
  if byte = 0x51 then some .nasdaqGlobalSelectMarket
  else if byte = 0x47 then some .nasdaqGlobalMarket
  else if byte = 0x53 then some .nasdaqCapitalMarket
  else if byte = 0x4E then some .nyse
  else if byte = 0x41 then some .nyseAmerican
  else if byte = 0x50 then some .nyseArca
  else if byte = 0x4D then some .nyseTexas
  else if byte = 0x5A then some .batsZ
  else if byte = 0x56 then some .investorsExchange
  else if byte = 0x20 then some .notAvailable
  else none

theorem ofByte?_toByte (value : MarketCategory) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : MarketCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCategory × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end MarketCategory

/-- Financial Status Indicator: one byte code -/
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

def ofByte? (byte : UInt8) : Option FinancialStatusIndicator :=
  if byte = 0x44 then some .deficient
  else if byte = 0x45 then some .delinquent
  else if byte = 0x51 then some .bankrupt
  else if byte = 0x53 then some .suspended
  else if byte = 0x47 then some .deficientAndBankrupt
  else if byte = 0x48 then some .deficientAndDelinquent
  else if byte = 0x4A then some .delinquentAndBankrupt
  else if byte = 0x4B then some .deficientDelinquentAndBankrupt
  else if byte = 0x43 then some .creationsAndRedemptionsSuspended
  else if byte = 0x4E then some .normal
  else if byte = 0x20 then some .notAvailable
  else none

theorem ofByte?_toByte (value : FinancialStatusIndicator) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : FinancialStatusIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinancialStatusIndicator × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : FinancialStatusIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FinancialStatusIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end FinancialStatusIndicator

/-- Round Lots Only: one byte code -/
inductive RoundLotsOnly where
  | yes -- Yes
  | no -- No
  deriving DecidableEq, Repr

namespace RoundLotsOnly

def toByte : RoundLotsOnly → UInt8
  | .yes => 0x59
  | .no => 0x4E

def ofByte? (byte : UInt8) : Option RoundLotsOnly :=
  if byte = 0x59 then some .yes
  else if byte = 0x4E then some .no
  else none

theorem ofByte?_toByte (value : RoundLotsOnly) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : RoundLotsOnly) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RoundLotsOnly × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : RoundLotsOnly) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RoundLotsOnly) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end RoundLotsOnly

/-- Issue Classification: one byte code -/
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

def ofByte? (byte : UInt8) : Option IssueClassification :=
  if byte = 0x41 then some .americanDepositaryShare
  else if byte = 0x42 then some .bond
  else if byte = 0x43 then some .commonStock
  else if byte = 0x46 then some .depositoryReceipt
  else if byte = 0x49 then some .sec144A
  else if byte = 0x4C then some .limitedPartnership
  else if byte = 0x4E then some .notes
  else if byte = 0x4F then some .ordinaryShare
  else if byte = 0x50 then some .preferredStock
  else if byte = 0x51 then some .otherSecurities
  else if byte = 0x52 then some .right
  else if byte = 0x53 then some .sharesOfBeneficialInterest
  else if byte = 0x54 then some .convertibleDebenture
  else if byte = 0x55 then some .unit
  else if byte = 0x56 then some .unitsOfBeneficialInterest
  else if byte = 0x57 then some .warrant
  else none

theorem ofByte?_toByte (value : IssueClassification) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : IssueClassification) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IssueClassification × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : IssueClassification) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IssueClassification) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end IssueClassification

/-- Authenticity: one byte code -/
inductive Authenticity where
  | liveProduction -- Live Production
  | test -- Test
  deriving DecidableEq, Repr

namespace Authenticity

def toByte : Authenticity → UInt8
  | .liveProduction => 0x50
  | .test => 0x54

def ofByte? (byte : UInt8) : Option Authenticity :=
  if byte = 0x50 then some .liveProduction
  else if byte = 0x54 then some .test
  else none

theorem ofByte?_toByte (value : Authenticity) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : Authenticity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Authenticity × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : Authenticity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Authenticity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end Authenticity

/-- Short Sale Threshold Indicator: one byte code -/
inductive ShortSaleThresholdIndicator where
  | restricted -- Restricted
  | notRestricted -- Not Restricted
  | notAvailable -- Not Available
  deriving DecidableEq, Repr

namespace ShortSaleThresholdIndicator

def toByte : ShortSaleThresholdIndicator → UInt8
  | .restricted => 0x59
  | .notRestricted => 0x4E
  | .notAvailable => 0x20

def ofByte? (byte : UInt8) : Option ShortSaleThresholdIndicator :=
  if byte = 0x59 then some .restricted
  else if byte = 0x4E then some .notRestricted
  else if byte = 0x20 then some .notAvailable
  else none

theorem ofByte?_toByte (value : ShortSaleThresholdIndicator) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : ShortSaleThresholdIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSaleThresholdIndicator × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSaleThresholdIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ShortSaleThresholdIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end ShortSaleThresholdIndicator

/-- Ipo Flag: one byte code -/
inductive IpoFlag where
  | setUpForIpoRelease -- Set Up For Ipo Release
  | notSetUpForIpoRelease -- Not Set Up For Ipo Release
  | nonIpoNewListedSecurity -- Non Ipo New Listed Security
  | notAvailable -- Not Available
  deriving DecidableEq, Repr

namespace IpoFlag

def toByte : IpoFlag → UInt8
  | .setUpForIpoRelease => 0x59
  | .notSetUpForIpoRelease => 0x4E
  | .nonIpoNewListedSecurity => 0x5A
  | .notAvailable => 0x20

def ofByte? (byte : UInt8) : Option IpoFlag :=
  if byte = 0x59 then some .setUpForIpoRelease
  else if byte = 0x4E then some .notSetUpForIpoRelease
  else if byte = 0x5A then some .nonIpoNewListedSecurity
  else if byte = 0x20 then some .notAvailable
  else none

theorem ofByte?_toByte (value : IpoFlag) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : IpoFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IpoFlag × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : IpoFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IpoFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end IpoFlag

/-- Luld Reference Price Tier: one byte code -/
inductive LuldReferencePriceTier where
  | tier1 -- Tier 1
  | tier2 -- Tier 2
  | notAvailable -- Not Available
  deriving DecidableEq, Repr

namespace LuldReferencePriceTier

def toByte : LuldReferencePriceTier → UInt8
  | .tier1 => 0x31
  | .tier2 => 0x32
  | .notAvailable => 0x20

def ofByte? (byte : UInt8) : Option LuldReferencePriceTier :=
  if byte = 0x31 then some .tier1
  else if byte = 0x32 then some .tier2
  else if byte = 0x20 then some .notAvailable
  else none

theorem ofByte?_toByte (value : LuldReferencePriceTier) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : LuldReferencePriceTier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LuldReferencePriceTier × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : LuldReferencePriceTier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LuldReferencePriceTier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end LuldReferencePriceTier

/-- Etp Flag: one byte code -/
inductive EtpFlag where
  | etp -- Etp
  | notEtp -- Not Etp
  | notAvailable -- Not Available
  deriving DecidableEq, Repr

namespace EtpFlag

def toByte : EtpFlag → UInt8
  | .etp => 0x59
  | .notEtp => 0x4E
  | .notAvailable => 0x20

def ofByte? (byte : UInt8) : Option EtpFlag :=
  if byte = 0x59 then some .etp
  else if byte = 0x4E then some .notEtp
  else if byte = 0x20 then some .notAvailable
  else none

theorem ofByte?_toByte (value : EtpFlag) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : EtpFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EtpFlag × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : EtpFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EtpFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end EtpFlag

/-- Inverse Indicator: one byte code -/
inductive InverseIndicator where
  | inverseEtp -- Inverse Etp
  | notInverseEtp -- Not Inverse Etp
  deriving DecidableEq, Repr

namespace InverseIndicator

def toByte : InverseIndicator → UInt8
  | .inverseEtp => 0x59
  | .notInverseEtp => 0x4E

def ofByte? (byte : UInt8) : Option InverseIndicator :=
  if byte = 0x59 then some .inverseEtp
  else if byte = 0x4E then some .notInverseEtp
  else none

theorem ofByte?_toByte (value : InverseIndicator) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : InverseIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InverseIndicator × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : InverseIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InverseIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end InverseIndicator

/-- Trading State: one byte code -/
inductive TradingState where
  | halted -- Halted
  | paused -- Paused
  | quotationOnlyPeriod -- Quotation Only Period
  | trading -- Trading
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .halted => 0x48
  | .paused => 0x50
  | .quotationOnlyPeriod => 0x51
  | .trading => 0x54

def ofByte? (byte : UInt8) : Option TradingState :=
  if byte = 0x48 then some .halted
  else if byte = 0x50 then some .paused
  else if byte = 0x51 then some .quotationOnlyPeriod
  else if byte = 0x54 then some .trading
  else none

theorem ofByte?_toByte (value : TradingState) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : TradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingState × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end TradingState

/-- Reg Sho Action: one byte code -/
inductive RegShoAction where
  | noPriceTest -- No Price Test
  | regShoShortSalePriceTestRestriction -- Reg Sho Short Sale Price Test Restriction
  | testRestrictionRemains -- Test Restriction Remains
  deriving DecidableEq, Repr

namespace RegShoAction

def toByte : RegShoAction → UInt8
  | .noPriceTest => 0x30
  | .regShoShortSalePriceTestRestriction => 0x31
  | .testRestrictionRemains => 0x32

def ofByte? (byte : UInt8) : Option RegShoAction :=
  if byte = 0x30 then some .noPriceTest
  else if byte = 0x31 then some .regShoShortSalePriceTestRestriction
  else if byte = 0x32 then some .testRestrictionRemains
  else none

theorem ofByte?_toByte (value : RegShoAction) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : RegShoAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RegShoAction × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : RegShoAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RegShoAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end RegShoAction

/-- Primary Market Maker: one byte code -/
inductive PrimaryMarketMaker where
  | primary -- Primary
  | nonPrimary -- Non Primary
  deriving DecidableEq, Repr

namespace PrimaryMarketMaker

def toByte : PrimaryMarketMaker → UInt8
  | .primary => 0x59
  | .nonPrimary => 0x4E

def ofByte? (byte : UInt8) : Option PrimaryMarketMaker :=
  if byte = 0x59 then some .primary
  else if byte = 0x4E then some .nonPrimary
  else none

theorem ofByte?_toByte (value : PrimaryMarketMaker) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : PrimaryMarketMaker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrimaryMarketMaker × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : PrimaryMarketMaker) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrimaryMarketMaker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end PrimaryMarketMaker

/-- Market Maker Mode: one byte code -/
inductive MarketMakerMode where
  | normal -- Normal
  | passive -- Passive
  | syndicate -- Syndicate
  | preSyndicate -- Pre Syndicate
  | penalty -- Penalty
  deriving DecidableEq, Repr

namespace MarketMakerMode

def toByte : MarketMakerMode → UInt8
  | .normal => 0x4E
  | .passive => 0x50
  | .syndicate => 0x53
  | .preSyndicate => 0x52
  | .penalty => 0x4C

def ofByte? (byte : UInt8) : Option MarketMakerMode :=
  if byte = 0x4E then some .normal
  else if byte = 0x50 then some .passive
  else if byte = 0x53 then some .syndicate
  else if byte = 0x52 then some .preSyndicate
  else if byte = 0x4C then some .penalty
  else none

theorem ofByte?_toByte (value : MarketMakerMode) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : MarketMakerMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketMakerMode × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketMakerMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketMakerMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end MarketMakerMode

/-- Market Participant State: one byte code -/
inductive MarketParticipantState where
  | active -- Active
  | excused -- Excused
  | withdrawn -- Withdrawn
  | suspended -- Suspended
  | deleted -- Deleted
  deriving DecidableEq, Repr

namespace MarketParticipantState

def toByte : MarketParticipantState → UInt8
  | .active => 0x41
  | .excused => 0x45
  | .withdrawn => 0x57
  | .suspended => 0x53
  | .deleted => 0x44

def ofByte? (byte : UInt8) : Option MarketParticipantState :=
  if byte = 0x41 then some .active
  else if byte = 0x45 then some .excused
  else if byte = 0x57 then some .withdrawn
  else if byte = 0x53 then some .suspended
  else if byte = 0x44 then some .deleted
  else none

theorem ofByte?_toByte (value : MarketParticipantState) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : MarketParticipantState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketParticipantState × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketParticipantState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketParticipantState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end MarketParticipantState

/-- Breached Level: one byte code -/
inductive BreachedLevel where
  | level1 -- Level 1
  | level2 -- Level 2
  | level3 -- Level 3
  deriving DecidableEq, Repr

namespace BreachedLevel

def toByte : BreachedLevel → UInt8
  | .level1 => 0x31
  | .level2 => 0x32
  | .level3 => 0x33

def ofByte? (byte : UInt8) : Option BreachedLevel :=
  if byte = 0x31 then some .level1
  else if byte = 0x32 then some .level2
  else if byte = 0x33 then some .level3
  else none

theorem ofByte?_toByte (value : BreachedLevel) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : BreachedLevel) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BreachedLevel × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : BreachedLevel) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BreachedLevel) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end BreachedLevel

/-- Ipo Quotation Release Qualifier: one byte code -/
inductive IpoQuotationReleaseQualifier where
  | anticipatedQuotationReleaseTime -- Anticipated Quotation Release Time
  | ipoReleaseCanceledOrPostponed -- Ipo Release Canceled Or Postponed
  deriving DecidableEq, Repr

namespace IpoQuotationReleaseQualifier

def toByte : IpoQuotationReleaseQualifier → UInt8
  | .anticipatedQuotationReleaseTime => 0x41
  | .ipoReleaseCanceledOrPostponed => 0x43

def ofByte? (byte : UInt8) : Option IpoQuotationReleaseQualifier :=
  if byte = 0x41 then some .anticipatedQuotationReleaseTime
  else if byte = 0x43 then some .ipoReleaseCanceledOrPostponed
  else none

theorem ofByte?_toByte (value : IpoQuotationReleaseQualifier) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : IpoQuotationReleaseQualifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IpoQuotationReleaseQualifier × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : IpoQuotationReleaseQualifier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IpoQuotationReleaseQualifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end IpoQuotationReleaseQualifier

/-- Market Code: one byte code -/
inductive MarketCode where
  | nasdaq -- Nasdaq
  | nasdaqTexas -- Nasdaq Texas
  | psx -- Psx
  deriving DecidableEq, Repr

namespace MarketCode

def toByte : MarketCode → UInt8
  | .nasdaq => 0x51
  | .nasdaqTexas => 0x42
  | .psx => 0x58

def ofByte? (byte : UInt8) : Option MarketCode :=
  if byte = 0x51 then some .nasdaq
  else if byte = 0x42 then some .nasdaqTexas
  else if byte = 0x58 then some .psx
  else none

theorem ofByte?_toByte (value : MarketCode) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : MarketCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCode × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end MarketCode

/-- Operational Halt Action: one byte code -/
inductive OperationalHaltAction where
  | halted -- Halted
  | tradingResumed -- Trading Resumed
  deriving DecidableEq, Repr

namespace OperationalHaltAction

def toByte : OperationalHaltAction → UInt8
  | .halted => 0x48
  | .tradingResumed => 0x54

def ofByte? (byte : UInt8) : Option OperationalHaltAction :=
  if byte = 0x48 then some .halted
  else if byte = 0x54 then some .tradingResumed
  else none

theorem ofByte?_toByte (value : OperationalHaltAction) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : OperationalHaltAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OperationalHaltAction × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : OperationalHaltAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OperationalHaltAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end OperationalHaltAction

/-- Buy Sell Indicator: one byte code -/
inductive BuySellIndicator where
  | buy -- Buy
  | sell -- Sell
  deriving DecidableEq, Repr

namespace BuySellIndicator

def toByte : BuySellIndicator → UInt8
  | .buy => 0x42
  | .sell => 0x53

def ofByte? (byte : UInt8) : Option BuySellIndicator :=
  if byte = 0x42 then some .buy
  else if byte = 0x53 then some .sell
  else none

theorem ofByte?_toByte (value : BuySellIndicator) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : BuySellIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuySellIndicator × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : BuySellIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BuySellIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end BuySellIndicator

/-- Printable: one byte code -/
inductive Printable where
  | no -- No
  | yes -- Yes
  deriving DecidableEq, Repr

namespace Printable

def toByte : Printable → UInt8
  | .no => 0x4E
  | .yes => 0x59

def ofByte? (byte : UInt8) : Option Printable :=
  if byte = 0x4E then some .no
  else if byte = 0x59 then some .yes
  else none

theorem ofByte?_toByte (value : Printable) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : Printable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Printable × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : Printable) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Printable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end Printable

/-- Cross Type: one byte code -/
inductive CrossType where
  | opening -- Opening
  | closing -- Closing
  | haltedOrPaused -- Halted Or Paused
  | extendedClose -- Extended Close
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .opening => 0x4F
  | .closing => 0x43
  | .haltedOrPaused => 0x48
  | .extendedClose => 0x41

def ofByte? (byte : UInt8) : Option CrossType :=
  if byte = 0x4F then some .opening
  else if byte = 0x43 then some .closing
  else if byte = 0x48 then some .haltedOrPaused
  else if byte = 0x41 then some .extendedClose
  else none

theorem ofByte?_toByte (value : CrossType) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : CrossType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossType × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CrossType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end CrossType

/-- Imbalance Direction: one byte code -/
inductive ImbalanceDirection where
  | buy -- Buy
  | sell -- Sell
  | none_ -- None
  | insufficientOrders -- Insufficient Orders
  | paused -- Paused
  deriving DecidableEq, Repr

namespace ImbalanceDirection

def toByte : ImbalanceDirection → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .none_ => 0x4E
  | .insufficientOrders => 0x4F
  | .paused => 0x50

def ofByte? (byte : UInt8) : Option ImbalanceDirection :=
  if byte = 0x42 then some .buy
  else if byte = 0x53 then some .sell
  else if byte = 0x4E then some .none_
  else if byte = 0x4F then some .insufficientOrders
  else if byte = 0x50 then some .paused
  else none

theorem ofByte?_toByte (value : ImbalanceDirection) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : ImbalanceDirection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceDirection × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceDirection) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ImbalanceDirection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end ImbalanceDirection

/-- Price Variation Indicator: one byte code -/
inductive PriceVariationIndicator where
  | lessThan1Percent -- Less Than 1 Percent
  | lessThan2Percent -- Less Than 2 Percent
  | lessThan3Percent -- Less Than 3 Percent
  | lessThan4Percent -- Less Than 4 Percent
  | lessThan5Percent -- Less Than 5 Percent
  | lessThan6Percent -- Less Than 6 Percent
  | lessThan7Percent -- Less Than 7 Percent
  | lessThan8Percent -- Less Than 8 Percent
  | lessThan9Percent -- Less Than 9 Percent
  | lessThan10Percent -- Less Than 10 Percent
  | lessThan20Percent -- Less Than 20 Percent
  | lessThan30Percent -- Less Than 30 Percent
  | moreThan30Percent -- More Than 30 Percent
  | notAvailable -- Not Available
  deriving DecidableEq, Repr

namespace PriceVariationIndicator

def toByte : PriceVariationIndicator → UInt8
  | .lessThan1Percent => 0x4C
  | .lessThan2Percent => 0x31
  | .lessThan3Percent => 0x32
  | .lessThan4Percent => 0x33
  | .lessThan5Percent => 0x34
  | .lessThan6Percent => 0x35
  | .lessThan7Percent => 0x36
  | .lessThan8Percent => 0x37
  | .lessThan9Percent => 0x38
  | .lessThan10Percent => 0x39
  | .lessThan20Percent => 0x41
  | .lessThan30Percent => 0x42
  | .moreThan30Percent => 0x43
  | .notAvailable => 0x20

def ofByte? (byte : UInt8) : Option PriceVariationIndicator :=
  if byte = 0x4C then some .lessThan1Percent
  else if byte = 0x31 then some .lessThan2Percent
  else if byte = 0x32 then some .lessThan3Percent
  else if byte = 0x33 then some .lessThan4Percent
  else if byte = 0x34 then some .lessThan5Percent
  else if byte = 0x35 then some .lessThan6Percent
  else if byte = 0x36 then some .lessThan7Percent
  else if byte = 0x37 then some .lessThan8Percent
  else if byte = 0x38 then some .lessThan9Percent
  else if byte = 0x39 then some .lessThan10Percent
  else if byte = 0x41 then some .lessThan20Percent
  else if byte = 0x42 then some .lessThan30Percent
  else if byte = 0x43 then some .moreThan30Percent
  else if byte = 0x20 then some .notAvailable
  else none

theorem ofByte?_toByte (value : PriceVariationIndicator) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : PriceVariationIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceVariationIndicator × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceVariationIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceVariationIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end PriceVariationIndicator

/-- Interest Flag: one byte code -/
inductive InterestFlag where
  | buySide -- Buy Side
  | sellSide -- Sell Side
  | bothSides -- Both Sides
  | noRpiOrdersAvailable -- No Rpi Orders Available
  deriving DecidableEq, Repr

namespace InterestFlag

def toByte : InterestFlag → UInt8
  | .buySide => 0x42
  | .sellSide => 0x53
  | .bothSides => 0x41
  | .noRpiOrdersAvailable => 0x4E

def ofByte? (byte : UInt8) : Option InterestFlag :=
  if byte = 0x42 then some .buySide
  else if byte = 0x53 then some .sellSide
  else if byte = 0x41 then some .bothSides
  else if byte = 0x4E then some .noRpiOrdersAvailable
  else none

theorem ofByte?_toByte (value : InterestFlag) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : InterestFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InterestFlag × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : InterestFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InterestFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end InterestFlag

/-- Open Eligibility Status: one byte code -/
inductive OpenEligibilityStatus where
  | notEligible -- Not Eligible
  | eligible -- Eligible
  deriving DecidableEq, Repr

namespace OpenEligibilityStatus

def toByte : OpenEligibilityStatus → UInt8
  | .notEligible => 0x4E
  | .eligible => 0x59

def ofByte? (byte : UInt8) : Option OpenEligibilityStatus :=
  if byte = 0x4E then some .notEligible
  else if byte = 0x59 then some .eligible
  else none

theorem ofByte?_toByte (value : OpenEligibilityStatus) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : OpenEligibilityStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenEligibilityStatus × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenEligibilityStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenEligibilityStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end OpenEligibilityStatus

/-- System Event Message: 11 bytes -/
structure SystemEventMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ EventCode.encode message.eventCode

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ stockLocate, trackingNumber, timestamp, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [EventCode.decode_encode, Option.bind_some]
  rfl

end SystemEventMessage

/-- Stock Directory Message: 38 bytes -/
structure StockDirectoryMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
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
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ Alpha.encode message.stock
    ++ MarketCategory.encode message.marketCategory
    ++ FinancialStatusIndicator.encode message.financialStatusIndicator
    ++ encodeUInt 4 message.roundLotSize
    ++ RoundLotsOnly.encode message.roundLotsOnly
    ++ IssueClassification.encode message.issueClassification
    ++ Alpha.encode message.issueSubType
    ++ Authenticity.encode message.authenticity
    ++ ShortSaleThresholdIndicator.encode message.shortSaleThresholdIndicator
    ++ IpoFlag.encode message.ipoFlag
    ++ LuldReferencePriceTier.encode message.luldReferencePriceTier
    ++ EtpFlag.encode message.etpFlag
    ++ encodeUInt 4 message.etpLeverageFactor
    ++ InverseIndicator.encode message.inverseIndicator

def decode (bytes : List UInt8) : Option (StockDirectoryMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
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
  pure ({ stockLocate, trackingNumber, timestamp, stock, marketCategory, financialStatusIndicator, roundLotSize, roundLotsOnly, issueClassification, issueSubType, authenticity, shortSaleThresholdIndicator, ipoFlag, luldReferencePriceTier, etpFlag, etpLeverageFactor, inverseIndicator }, bytes)

@[simp] theorem encode_length (message : StockDirectoryMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, MarketCategory.encode_length, FinancialStatusIndicator.encode_length, RoundLotsOnly.encode_length, IssueClassification.encode_length, Authenticity.encode_length, ShortSaleThresholdIndicator.encode_length, IpoFlag.encode_length, LuldReferencePriceTier.encode_length, EtpFlag.encode_length, InverseIndicator.encode_length]

theorem encode_length_pos (message : StockDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [MarketCategory.decode_encode]
  simp only [Option.bind_some]
  rw [FinancialStatusIndicator.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [RoundLotsOnly.decode_encode]
  simp only [Option.bind_some]
  rw [IssueClassification.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Authenticity.decode_encode]
  simp only [Option.bind_some]
  rw [ShortSaleThresholdIndicator.decode_encode]
  simp only [Option.bind_some]
  rw [IpoFlag.decode_encode]
  simp only [Option.bind_some]
  rw [LuldReferencePriceTier.decode_encode]
  simp only [Option.bind_some]
  rw [EtpFlag.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [InverseIndicator.decode_encode, Option.bind_some]
  rfl

end StockDirectoryMessage

/-- Stock Trading Action Message: 24 bytes -/
structure StockTradingActionMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  stock : Alpha 8
  tradingState : TradingState
  reserved : Alpha 1
  reasonCode : Alpha 4
  deriving DecidableEq, Repr

namespace StockTradingActionMessage

def encode (message : StockTradingActionMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ Alpha.encode message.stock
    ++ TradingState.encode message.tradingState
    ++ Alpha.encode message.reserved
    ++ Alpha.encode message.reasonCode

def decode (bytes : List UInt8) : Option (StockTradingActionMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← Alpha.decode 4 bytes
  pure ({ stockLocate, trackingNumber, timestamp, stock, tradingState, reserved, reasonCode }, bytes)

@[simp] theorem encode_length (message : StockTradingActionMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradingState.encode_length]

theorem encode_length_pos (message : StockTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [TradingState.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end StockTradingActionMessage

/-- Reg Sho Short Sale Price Test Restricted Indicator Message: 19 bytes -/
structure RegShoShortSalePriceTestRestrictedIndicatorMessage where
  locateCode : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  stock : Alpha 8
  regShoAction : RegShoAction
  deriving DecidableEq, Repr

namespace RegShoShortSalePriceTestRestrictedIndicatorMessage

def encode (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : List UInt8 :=
  encodeUInt 2 message.locateCode
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ Alpha.encode message.stock
    ++ RegShoAction.encode message.regShoAction

def decode (bytes : List UInt8) : Option (RegShoShortSalePriceTestRestrictedIndicatorMessage × List UInt8) := do
  let (locateCode, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (regShoAction, bytes) ← RegShoAction.decode bytes
  pure ({ locateCode, trackingNumber, timestamp, stock, regShoAction }, bytes)

@[simp] theorem encode_length (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, RegShoAction.encode_length]

theorem encode_length_pos (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RegShoAction.decode_encode, Option.bind_some]
  rfl

end RegShoShortSalePriceTestRestrictedIndicatorMessage

/-- Market Participant Position Message: 25 bytes -/
structure MarketParticipantPositionMessage where
  stockLocate : BitVec 16
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
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ Alpha.encode message.mpid
    ++ Alpha.encode message.stock
    ++ PrimaryMarketMaker.encode message.primaryMarketMaker
    ++ MarketMakerMode.encode message.marketMakerMode
    ++ MarketParticipantState.encode message.marketParticipantState

def decode (bytes : List UInt8) : Option (MarketParticipantPositionMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (primaryMarketMaker, bytes) ← PrimaryMarketMaker.decode bytes
  let (marketMakerMode, bytes) ← MarketMakerMode.decode bytes
  let (marketParticipantState, bytes) ← MarketParticipantState.decode bytes
  pure ({ stockLocate, trackingNumber, timestamp, mpid, stock, primaryMarketMaker, marketMakerMode, marketParticipantState }, bytes)

@[simp] theorem encode_length (message : MarketParticipantPositionMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, PrimaryMarketMaker.encode_length, MarketMakerMode.encode_length, MarketParticipantState.encode_length]

theorem encode_length_pos (message : MarketParticipantPositionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketParticipantPositionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [PrimaryMarketMaker.decode_encode]
  simp only [Option.bind_some]
  rw [MarketMakerMode.decode_encode]
  simp only [Option.bind_some]
  rw [MarketParticipantState.decode_encode, Option.bind_some]
  rfl

end MarketParticipantPositionMessage

/-- Mwcb Decline Level Message: 34 bytes -/
structure MwcbDeclineLevelMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  level1 : BitVec 64
  level2 : BitVec 64
  level3 : BitVec 64
  deriving DecidableEq, Repr

namespace MwcbDeclineLevelMessage

def encode (message : MwcbDeclineLevelMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ encodeUInt 8 message.level1
    ++ encodeUInt 8 message.level2
    ++ encodeUInt 8 message.level3

def decode (bytes : List UInt8) : Option (MwcbDeclineLevelMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (level1, bytes) ← decodeUInt 8 bytes
  let (level2, bytes) ← decodeUInt 8 bytes
  let (level3, bytes) ← decodeUInt 8 bytes
  pure ({ stockLocate, trackingNumber, timestamp, level1, level2, level3 }, bytes)

@[simp] theorem encode_length (message : MwcbDeclineLevelMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : MwcbDeclineLevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MwcbDeclineLevelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end MwcbDeclineLevelMessage

/-- Mwcb Status Level Message: 11 bytes -/
structure MwcbStatusLevelMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  breachedLevel : BreachedLevel
  deriving DecidableEq, Repr

namespace MwcbStatusLevelMessage

def encode (message : MwcbStatusLevelMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ BreachedLevel.encode message.breachedLevel

def decode (bytes : List UInt8) : Option (MwcbStatusLevelMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (breachedLevel, bytes) ← BreachedLevel.decode bytes
  pure ({ stockLocate, trackingNumber, timestamp, breachedLevel }, bytes)

@[simp] theorem encode_length (message : MwcbStatusLevelMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BreachedLevel.encode_length]

theorem encode_length_pos (message : MwcbStatusLevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MwcbStatusLevelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [BreachedLevel.decode_encode, Option.bind_some]
  rfl

end MwcbStatusLevelMessage

/-- Ipo Quoting Period Update: 27 bytes -/
structure IpoQuotingPeriodUpdate where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  stock : Alpha 8
  ipoQuotationReleaseTime : BitVec 32
  ipoQuotationReleaseQualifier : IpoQuotationReleaseQualifier
  ipoPrice : BitVec 32
  deriving DecidableEq, Repr

namespace IpoQuotingPeriodUpdate

def encode (message : IpoQuotingPeriodUpdate) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ Alpha.encode message.stock
    ++ encodeUInt 4 message.ipoQuotationReleaseTime
    ++ IpoQuotationReleaseQualifier.encode message.ipoQuotationReleaseQualifier
    ++ encodeUInt 4 message.ipoPrice

def decode (bytes : List UInt8) : Option (IpoQuotingPeriodUpdate × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (ipoQuotationReleaseTime, bytes) ← decodeUInt 4 bytes
  let (ipoQuotationReleaseQualifier, bytes) ← IpoQuotationReleaseQualifier.decode bytes
  let (ipoPrice, bytes) ← decodeUInt 4 bytes
  pure ({ stockLocate, trackingNumber, timestamp, stock, ipoQuotationReleaseTime, ipoQuotationReleaseQualifier, ipoPrice }, bytes)

@[simp] theorem encode_length (message : IpoQuotingPeriodUpdate) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, IpoQuotationReleaseQualifier.encode_length]

theorem encode_length_pos (message : IpoQuotingPeriodUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IpoQuotingPeriodUpdate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [IpoQuotationReleaseQualifier.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end IpoQuotingPeriodUpdate

/-- Luld Auction Collar Message: 34 bytes -/
structure LuldAuctionCollarMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  stock : Alpha 8
  auctionCollarReferencePrice : BitVec 32
  upperAuctionCollarPrice : BitVec 32
  lowerAuctionCollarPrice : BitVec 32
  auctionCollarExtension : BitVec 32
  deriving DecidableEq, Repr

namespace LuldAuctionCollarMessage

def encode (message : LuldAuctionCollarMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ Alpha.encode message.stock
    ++ encodeUInt 4 message.auctionCollarReferencePrice
    ++ encodeUInt 4 message.upperAuctionCollarPrice
    ++ encodeUInt 4 message.lowerAuctionCollarPrice
    ++ encodeUInt 4 message.auctionCollarExtension

def decode (bytes : List UInt8) : Option (LuldAuctionCollarMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (auctionCollarReferencePrice, bytes) ← decodeUInt 4 bytes
  let (upperAuctionCollarPrice, bytes) ← decodeUInt 4 bytes
  let (lowerAuctionCollarPrice, bytes) ← decodeUInt 4 bytes
  let (auctionCollarExtension, bytes) ← decodeUInt 4 bytes
  pure ({ stockLocate, trackingNumber, timestamp, stock, auctionCollarReferencePrice, upperAuctionCollarPrice, lowerAuctionCollarPrice, auctionCollarExtension }, bytes)

@[simp] theorem encode_length (message : LuldAuctionCollarMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LuldAuctionCollarMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LuldAuctionCollarMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end LuldAuctionCollarMessage

/-- Operational Halt Message: 20 bytes -/
structure OperationalHaltMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  stock : Alpha 8
  marketCode : MarketCode
  operationalHaltAction : OperationalHaltAction
  deriving DecidableEq, Repr

namespace OperationalHaltMessage

def encode (message : OperationalHaltMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ Alpha.encode message.stock
    ++ MarketCode.encode message.marketCode
    ++ OperationalHaltAction.encode message.operationalHaltAction

def decode (bytes : List UInt8) : Option (OperationalHaltMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (marketCode, bytes) ← MarketCode.decode bytes
  let (operationalHaltAction, bytes) ← OperationalHaltAction.decode bytes
  pure ({ stockLocate, trackingNumber, timestamp, stock, marketCode, operationalHaltAction }, bytes)

@[simp] theorem encode_length (message : OperationalHaltMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, MarketCode.encode_length, OperationalHaltAction.encode_length]

theorem encode_length_pos (message : OperationalHaltMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OperationalHaltMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [MarketCode.decode_encode]
  simp only [Option.bind_some]
  rw [OperationalHaltAction.decode_encode, Option.bind_some]
  rfl

end OperationalHaltMessage

/-- Add Order No Mpid Attribution Message: 35 bytes -/
structure AddOrderNoMpidAttributionMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  orderReferenceNumber : BitVec 64
  buySellIndicator : BuySellIndicator
  shares : BitVec 32
  stock : Alpha 8
  price : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderNoMpidAttributionMessage

def encode (message : AddOrderNoMpidAttributionMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ encodeUInt 8 message.orderReferenceNumber
    ++ BuySellIndicator.encode message.buySellIndicator
    ++ encodeUInt 4 message.shares
    ++ Alpha.encode message.stock
    ++ encodeUInt 4 message.price

def decode (bytes : List UInt8) : Option (AddOrderNoMpidAttributionMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ stockLocate, trackingNumber, timestamp, orderReferenceNumber, buySellIndicator, shares, stock, price }, bytes)

@[simp] theorem encode_length (message : AddOrderNoMpidAttributionMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BuySellIndicator.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderNoMpidAttributionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderNoMpidAttributionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [BuySellIndicator.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end AddOrderNoMpidAttributionMessage

/-- Add Order With Mpid Attribution Message: 39 bytes -/
structure AddOrderWithMpidAttributionMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  orderReferenceNumber : BitVec 64
  buySellIndicator : BuySellIndicator
  shares : BitVec 32
  stock : Alpha 8
  price : BitVec 32
  attribution : Alpha 4
  deriving DecidableEq, Repr

namespace AddOrderWithMpidAttributionMessage

def encode (message : AddOrderWithMpidAttributionMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ encodeUInt 8 message.orderReferenceNumber
    ++ BuySellIndicator.encode message.buySellIndicator
    ++ encodeUInt 4 message.shares
    ++ Alpha.encode message.stock
    ++ encodeUInt 4 message.price
    ++ Alpha.encode message.attribution

def decode (bytes : List UInt8) : Option (AddOrderWithMpidAttributionMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (attribution, bytes) ← Alpha.decode 4 bytes
  pure ({ stockLocate, trackingNumber, timestamp, orderReferenceNumber, buySellIndicator, shares, stock, price, attribution }, bytes)

@[simp] theorem encode_length (message : AddOrderWithMpidAttributionMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BuySellIndicator.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderWithMpidAttributionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderWithMpidAttributionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [BuySellIndicator.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end AddOrderWithMpidAttributionMessage

/-- Order Executed Message: 30 bytes -/
structure OrderExecutedMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  orderReferenceNumber : BitVec 64
  executedShares : BitVec 32
  matchNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ encodeUInt 8 message.orderReferenceNumber
    ++ encodeUInt 4 message.executedShares
    ++ encodeUInt 8 message.matchNumber

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (executedShares, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  pure ({ stockLocate, trackingNumber, timestamp, orderReferenceNumber, executedShares, matchNumber }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end OrderExecutedMessage

/-- Order Executed With Price Message: 35 bytes -/
structure OrderExecutedWithPriceMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  orderReferenceNumber : BitVec 64
  executedShares : BitVec 32
  matchNumber : BitVec 64
  printable : Printable
  executionPrice : BitVec 32
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ encodeUInt 8 message.orderReferenceNumber
    ++ encodeUInt 4 message.executedShares
    ++ encodeUInt 8 message.matchNumber
    ++ Printable.encode message.printable
    ++ encodeUInt 4 message.executionPrice

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (executedShares, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (printable, bytes) ← Printable.decode bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  pure ({ stockLocate, trackingNumber, timestamp, orderReferenceNumber, executedShares, matchNumber, printable, executionPrice }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length]

theorem encode_length_pos (message : OrderExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Printable.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end OrderExecutedWithPriceMessage

/-- Order Cancel Message: 22 bytes -/
structure OrderCancelMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  orderReferenceNumber : BitVec 64
  canceledShares : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ encodeUInt 8 message.orderReferenceNumber
    ++ encodeUInt 4 message.canceledShares

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (canceledShares, bytes) ← decodeUInt 4 bytes
  pure ({ stockLocate, trackingNumber, timestamp, orderReferenceNumber, canceledShares }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end OrderCancelMessage

/-- Order Delete Message: 18 bytes -/
structure OrderDeleteMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  orderReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ encodeUInt 8 message.orderReferenceNumber

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ stockLocate, trackingNumber, timestamp, orderReferenceNumber }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end OrderDeleteMessage

/-- Order Replace Message: 34 bytes -/
structure OrderReplaceMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  originalOrderReferenceNumber : BitVec 64
  newOrderReferenceNumber : BitVec 64
  shares : BitVec 32
  price : BitVec 32
  deriving DecidableEq, Repr

namespace OrderReplaceMessage

def encode (message : OrderReplaceMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ encodeUInt 8 message.originalOrderReferenceNumber
    ++ encodeUInt 8 message.newOrderReferenceNumber
    ++ encodeUInt 4 message.shares
    ++ encodeUInt 4 message.price

def decode (bytes : List UInt8) : Option (OrderReplaceMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (originalOrderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (newOrderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ stockLocate, trackingNumber, timestamp, originalOrderReferenceNumber, newOrderReferenceNumber, shares, price }, bytes)

@[simp] theorem encode_length (message : OrderReplaceMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderReplaceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end OrderReplaceMessage

/-- Non Cross Trade Message: 43 bytes -/
structure NonCrossTradeMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  orderReferenceNumber : BitVec 64
  buySellIndicator : BuySellIndicator
  shares : BitVec 32
  stock : Alpha 8
  price : BitVec 32
  matchNumber : BitVec 64
  deriving DecidableEq, Repr

namespace NonCrossTradeMessage

def encode (message : NonCrossTradeMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ encodeUInt 8 message.orderReferenceNumber
    ++ BuySellIndicator.encode message.buySellIndicator
    ++ encodeUInt 4 message.shares
    ++ Alpha.encode message.stock
    ++ encodeUInt 4 message.price
    ++ encodeUInt 8 message.matchNumber

def decode (bytes : List UInt8) : Option (NonCrossTradeMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  pure ({ stockLocate, trackingNumber, timestamp, orderReferenceNumber, buySellIndicator, shares, stock, price, matchNumber }, bytes)

@[simp] theorem encode_length (message : NonCrossTradeMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BuySellIndicator.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : NonCrossTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NonCrossTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [BuySellIndicator.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end NonCrossTradeMessage

/-- Cross Trade Message: 39 bytes -/
structure CrossTradeMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  crossShares : BitVec 64
  stock : Alpha 8
  crossPrice : BitVec 32
  matchNumber : BitVec 64
  crossType : CrossType
  deriving DecidableEq, Repr

namespace CrossTradeMessage

def encode (message : CrossTradeMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ encodeUInt 8 message.crossShares
    ++ Alpha.encode message.stock
    ++ encodeUInt 4 message.crossPrice
    ++ encodeUInt 8 message.matchNumber
    ++ CrossType.encode message.crossType

def decode (bytes : List UInt8) : Option (CrossTradeMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (crossShares, bytes) ← decodeUInt 8 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (crossPrice, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  pure ({ stockLocate, trackingNumber, timestamp, crossShares, stock, crossPrice, matchNumber, crossType }, bytes)

@[simp] theorem encode_length (message : CrossTradeMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, CrossType.encode_length]

theorem encode_length_pos (message : CrossTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [CrossType.decode_encode, Option.bind_some]
  rfl

end CrossTradeMessage

/-- Broken Trade Message: 18 bytes -/
structure BrokenTradeMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  matchNumber : BitVec 64
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ encodeUInt 8 message.matchNumber

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  pure ({ stockLocate, trackingNumber, timestamp, matchNumber }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end BrokenTradeMessage

/-- Net Order Imbalance Indicator Message: 49 bytes -/
structure NetOrderImbalanceIndicatorMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  pairedShares : BitVec 64
  imbalanceShares : BitVec 64
  imbalanceDirection : ImbalanceDirection
  stock : Alpha 8
  farPrice : BitVec 32
  nearPrice : BitVec 32
  currentReferencePrice : BitVec 32
  crossType : CrossType
  priceVariationIndicator : PriceVariationIndicator
  deriving DecidableEq, Repr

namespace NetOrderImbalanceIndicatorMessage

def encode (message : NetOrderImbalanceIndicatorMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ encodeUInt 8 message.pairedShares
    ++ encodeUInt 8 message.imbalanceShares
    ++ ImbalanceDirection.encode message.imbalanceDirection
    ++ Alpha.encode message.stock
    ++ encodeUInt 4 message.farPrice
    ++ encodeUInt 4 message.nearPrice
    ++ encodeUInt 4 message.currentReferencePrice
    ++ CrossType.encode message.crossType
    ++ PriceVariationIndicator.encode message.priceVariationIndicator

def decode (bytes : List UInt8) : Option (NetOrderImbalanceIndicatorMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (pairedShares, bytes) ← decodeUInt 8 bytes
  let (imbalanceShares, bytes) ← decodeUInt 8 bytes
  let (imbalanceDirection, bytes) ← ImbalanceDirection.decode bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (farPrice, bytes) ← decodeUInt 4 bytes
  let (nearPrice, bytes) ← decodeUInt 4 bytes
  let (currentReferencePrice, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (priceVariationIndicator, bytes) ← PriceVariationIndicator.decode bytes
  pure ({ stockLocate, trackingNumber, timestamp, pairedShares, imbalanceShares, imbalanceDirection, stock, farPrice, nearPrice, currentReferencePrice, crossType, priceVariationIndicator }, bytes)

@[simp] theorem encode_length (message : NetOrderImbalanceIndicatorMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ImbalanceDirection.encode_length, Alpha.encode_length, CrossType.encode_length, PriceVariationIndicator.encode_length]

theorem encode_length_pos (message : NetOrderImbalanceIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetOrderImbalanceIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [ImbalanceDirection.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [CrossType.decode_encode]
  simp only [Option.bind_some]
  rw [PriceVariationIndicator.decode_encode, Option.bind_some]
  rfl

end NetOrderImbalanceIndicatorMessage

/-- Retail Price Improvement Indicator Message: 19 bytes -/
structure RetailPriceImprovementIndicatorMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  stock : Alpha 8
  interestFlag : InterestFlag
  deriving DecidableEq, Repr

namespace RetailPriceImprovementIndicatorMessage

def encode (message : RetailPriceImprovementIndicatorMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ Alpha.encode message.stock
    ++ InterestFlag.encode message.interestFlag

def decode (bytes : List UInt8) : Option (RetailPriceImprovementIndicatorMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (interestFlag, bytes) ← InterestFlag.decode bytes
  pure ({ stockLocate, trackingNumber, timestamp, stock, interestFlag }, bytes)

@[simp] theorem encode_length (message : RetailPriceImprovementIndicatorMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, InterestFlag.encode_length]

theorem encode_length_pos (message : RetailPriceImprovementIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetailPriceImprovementIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [InterestFlag.decode_encode, Option.bind_some]
  rfl

end RetailPriceImprovementIndicatorMessage

/-- Direct Listing With Capital Raise Price Discovery Message: 47 bytes -/
structure DirectListingWithCapitalRaisePriceDiscoveryMessage where
  stockLocate : BitVec 16
  trackingNumber : BitVec 16
  timestamp : BitVec 48
  stock : Alpha 8
  openEligibilityStatus : OpenEligibilityStatus
  minimumAllowablePrice : BitVec 32
  maximumAllowablePrice : BitVec 32
  nearExecutionPrice : BitVec 32
  nearExecutionTime : BitVec 64
  lowerPriceRangeCollar : BitVec 32
  upperPriceRangeCollar : BitVec 32
  deriving DecidableEq, Repr

namespace DirectListingWithCapitalRaisePriceDiscoveryMessage

def encode (message : DirectListingWithCapitalRaisePriceDiscoveryMessage) : List UInt8 :=
  encodeUInt 2 message.stockLocate
    ++ encodeUInt 2 message.trackingNumber
    ++ encodeUInt 6 message.timestamp
    ++ Alpha.encode message.stock
    ++ OpenEligibilityStatus.encode message.openEligibilityStatus
    ++ encodeUInt 4 message.minimumAllowablePrice
    ++ encodeUInt 4 message.maximumAllowablePrice
    ++ encodeUInt 4 message.nearExecutionPrice
    ++ encodeUInt 8 message.nearExecutionTime
    ++ encodeUInt 4 message.lowerPriceRangeCollar
    ++ encodeUInt 4 message.upperPriceRangeCollar

def decode (bytes : List UInt8) : Option (DirectListingWithCapitalRaisePriceDiscoveryMessage × List UInt8) := do
  let (stockLocate, bytes) ← decodeUInt 2 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (stock, bytes) ← Alpha.decode 8 bytes
  let (openEligibilityStatus, bytes) ← OpenEligibilityStatus.decode bytes
  let (minimumAllowablePrice, bytes) ← decodeUInt 4 bytes
  let (maximumAllowablePrice, bytes) ← decodeUInt 4 bytes
  let (nearExecutionPrice, bytes) ← decodeUInt 4 bytes
  let (nearExecutionTime, bytes) ← decodeUInt 8 bytes
  let (lowerPriceRangeCollar, bytes) ← decodeUInt 4 bytes
  let (upperPriceRangeCollar, bytes) ← decodeUInt 4 bytes
  pure ({ stockLocate, trackingNumber, timestamp, stock, openEligibilityStatus, minimumAllowablePrice, maximumAllowablePrice, nearExecutionPrice, nearExecutionTime, lowerPriceRangeCollar, upperPriceRangeCollar }, bytes)

@[simp] theorem encode_length (message : DirectListingWithCapitalRaisePriceDiscoveryMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OpenEligibilityStatus.encode_length]

theorem encode_length_pos (message : DirectListingWithCapitalRaisePriceDiscoveryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DirectListingWithCapitalRaisePriceDiscoveryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [OpenEligibilityStatus.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end DirectListingWithCapitalRaisePriceDiscoveryMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- 'S' 0x53
  | stockDirectoryMessage (message : StockDirectoryMessage) -- 'R' 0x52
  | stockTradingActionMessage (message : StockTradingActionMessage) -- 'H' 0x48
  | regShoShortSalePriceTestRestrictedIndicatorMessage (message : RegShoShortSalePriceTestRestrictedIndicatorMessage) -- 'Y' 0x59
  | marketParticipantPositionMessage (message : MarketParticipantPositionMessage) -- 'L' 0x4C
  | mwcbDeclineLevelMessage (message : MwcbDeclineLevelMessage) -- 'V' 0x56
  | mwcbStatusLevelMessage (message : MwcbStatusLevelMessage) -- 'W' 0x57
  | ipoQuotingPeriodUpdate (message : IpoQuotingPeriodUpdate) -- 'K' 0x4B
  | luldAuctionCollarMessage (message : LuldAuctionCollarMessage) -- 'J' 0x4A
  | operationalHaltMessage (message : OperationalHaltMessage) -- 'h' 0x68
  | addOrderNoMpidAttributionMessage (message : AddOrderNoMpidAttributionMessage) -- 'A' 0x41
  | addOrderWithMpidAttributionMessage (message : AddOrderWithMpidAttributionMessage) -- 'F' 0x46
  | orderExecutedMessage (message : OrderExecutedMessage) -- 'E' 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- 'C' 0x43
  | orderCancelMessage (message : OrderCancelMessage) -- 'X' 0x58
  | orderDeleteMessage (message : OrderDeleteMessage) -- 'D' 0x44
  | orderReplaceMessage (message : OrderReplaceMessage) -- 'U' 0x55
  | nonCrossTradeMessage (message : NonCrossTradeMessage) -- 'P' 0x50
  | crossTradeMessage (message : CrossTradeMessage) -- 'Q' 0x51
  | brokenTradeMessage (message : BrokenTradeMessage) -- 'B' 0x42
  | netOrderImbalanceIndicatorMessage (message : NetOrderImbalanceIndicatorMessage) -- 'I' 0x49
  | retailPriceImprovementIndicatorMessage (message : RetailPriceImprovementIndicatorMessage) -- 'N' 0x4E
  | directListingWithCapitalRaisePriceDiscoveryMessage (message : DirectListingWithCapitalRaisePriceDiscoveryMessage) -- 'O' 0x4F
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .stockDirectoryMessage _ => 82
  | .stockTradingActionMessage _ => 72
  | .regShoShortSalePriceTestRestrictedIndicatorMessage _ => 89
  | .marketParticipantPositionMessage _ => 76
  | .mwcbDeclineLevelMessage _ => 86
  | .mwcbStatusLevelMessage _ => 87
  | .ipoQuotingPeriodUpdate _ => 75
  | .luldAuctionCollarMessage _ => 74
  | .operationalHaltMessage _ => 104
  | .addOrderNoMpidAttributionMessage _ => 65
  | .addOrderWithMpidAttributionMessage _ => 70
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .orderCancelMessage _ => 88
  | .orderDeleteMessage _ => 68
  | .orderReplaceMessage _ => 85
  | .nonCrossTradeMessage _ => 80
  | .crossTradeMessage _ => 81
  | .brokenTradeMessage _ => 66
  | .netOrderImbalanceIndicatorMessage _ => 73
  | .retailPriceImprovementIndicatorMessage _ => 78
  | .directListingWithCapitalRaisePriceDiscoveryMessage _ => 79

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .stockDirectoryMessage message => StockDirectoryMessage.encode message
  | .stockTradingActionMessage message => StockTradingActionMessage.encode message
  | .regShoShortSalePriceTestRestrictedIndicatorMessage message => RegShoShortSalePriceTestRestrictedIndicatorMessage.encode message
  | .marketParticipantPositionMessage message => MarketParticipantPositionMessage.encode message
  | .mwcbDeclineLevelMessage message => MwcbDeclineLevelMessage.encode message
  | .mwcbStatusLevelMessage message => MwcbStatusLevelMessage.encode message
  | .ipoQuotingPeriodUpdate message => IpoQuotingPeriodUpdate.encode message
  | .luldAuctionCollarMessage message => LuldAuctionCollarMessage.encode message
  | .operationalHaltMessage message => OperationalHaltMessage.encode message
  | .addOrderNoMpidAttributionMessage message => AddOrderNoMpidAttributionMessage.encode message
  | .addOrderWithMpidAttributionMessage message => AddOrderWithMpidAttributionMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderReplaceMessage message => OrderReplaceMessage.encode message
  | .nonCrossTradeMessage message => NonCrossTradeMessage.encode message
  | .crossTradeMessage message => CrossTradeMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .netOrderImbalanceIndicatorMessage message => NetOrderImbalanceIndicatorMessage.encode message
  | .retailPriceImprovementIndicatorMessage message => RetailPriceImprovementIndicatorMessage.encode message
  | .directListingWithCapitalRaisePriceDiscoveryMessage message => DirectListingWithCapitalRaisePriceDiscoveryMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (StockDirectoryMessage.decode bytes).map fun (message, rest) => (.stockDirectoryMessage message, rest)
  else if tag = 72 then (StockTradingActionMessage.decode bytes).map fun (message, rest) => (.stockTradingActionMessage message, rest)
  else if tag = 89 then (RegShoShortSalePriceTestRestrictedIndicatorMessage.decode bytes).map fun (message, rest) => (.regShoShortSalePriceTestRestrictedIndicatorMessage message, rest)
  else if tag = 76 then (MarketParticipantPositionMessage.decode bytes).map fun (message, rest) => (.marketParticipantPositionMessage message, rest)
  else if tag = 86 then (MwcbDeclineLevelMessage.decode bytes).map fun (message, rest) => (.mwcbDeclineLevelMessage message, rest)
  else if tag = 87 then (MwcbStatusLevelMessage.decode bytes).map fun (message, rest) => (.mwcbStatusLevelMessage message, rest)
  else if tag = 75 then (IpoQuotingPeriodUpdate.decode bytes).map fun (message, rest) => (.ipoQuotingPeriodUpdate message, rest)
  else if tag = 74 then (LuldAuctionCollarMessage.decode bytes).map fun (message, rest) => (.luldAuctionCollarMessage message, rest)
  else if tag = 104 then (OperationalHaltMessage.decode bytes).map fun (message, rest) => (.operationalHaltMessage message, rest)
  else if tag = 65 then (AddOrderNoMpidAttributionMessage.decode bytes).map fun (message, rest) => (.addOrderNoMpidAttributionMessage message, rest)
  else if tag = 70 then (AddOrderWithMpidAttributionMessage.decode bytes).map fun (message, rest) => (.addOrderWithMpidAttributionMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 88 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 85 then (OrderReplaceMessage.decode bytes).map fun (message, rest) => (.orderReplaceMessage message, rest)
  else if tag = 80 then (NonCrossTradeMessage.decode bytes).map fun (message, rest) => (.nonCrossTradeMessage message, rest)
  else if tag = 81 then (CrossTradeMessage.decode bytes).map fun (message, rest) => (.crossTradeMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 73 then (NetOrderImbalanceIndicatorMessage.decode bytes).map fun (message, rest) => (.netOrderImbalanceIndicatorMessage message, rest)
  else if tag = 78 then (RetailPriceImprovementIndicatorMessage.decode bytes).map fun (message, rest) => (.retailPriceImprovementIndicatorMessage message, rest)
  else if tag = 79 then (DirectListingWithCapitalRaisePriceDiscoveryMessage.decode bytes).map fun (message, rest) => (.directListingWithCapitalRaisePriceDiscoveryMessage message, rest)
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
    ++ Payload.encode message.payload

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Payload.decode_encode, Option.bind_some]
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
  | mwcbDeclineLevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MwcbDeclineLevelMessage.encode_length]
    omega
  | mwcbStatusLevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MwcbStatusLevelMessage.encode_length]
    omega
  | ipoQuotingPeriodUpdate inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IpoQuotingPeriodUpdate.encode_length]
    omega
  | luldAuctionCollarMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LuldAuctionCollarMessage.encode_length]
    omega
  | operationalHaltMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OperationalHaltMessage.encode_length]
    omega
  | addOrderNoMpidAttributionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderNoMpidAttributionMessage.encode_length]
    omega
  | addOrderWithMpidAttributionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderWithMpidAttributionMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancelMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderReplaceMessage.encode_length]
    omega
  | nonCrossTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NonCrossTradeMessage.encode_length]
    omega
  | crossTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CrossTradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | netOrderImbalanceIndicatorMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NetOrderImbalanceIndicatorMessage.encode_length]
    omega
  | retailPriceImprovementIndicatorMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RetailPriceImprovementIndicatorMessage.encode_length]
    omega
  | directListingWithCapitalRaisePriceDiscoveryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, DirectListingWithCapitalRaisePriceDiscoveryMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

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
    ++ encodeUInt 8 message.sequenceNumber
    ++ encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ encodeMany Message.encode message.message.val

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
  simp only [Alpha.encode_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode]
  simp only [Option.bind_some]
  simp only [message.message.length_lt, ↓reduceDIte]
  rfl

end Packet

end Omi.NasdaqNsmequitiesTotalviewItchV502023
