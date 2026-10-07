import Wire

/-!
# The Securities Industry Automation Corporation Output v6.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Administrative Message is not framed: its length Message Data Length is not an integer it reads.

Note: Bbo Indicator chooses the Best Bid Appendage or Best Offer Appendage or Best Bid And Offer Appendage attached, or none: it is written from the choice, and a value it does not list is not decoded.

Note: Block Pad Byte pads to a 2 byte boundary: it is read as the bytes left to the end of the frame, fewer than 2, and the frame's length is trusted to keep the boundary.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.SiacOpraOutputObiV62

/-- Data Feed Indicator: one byte code -/
def DataFeedIndicator.codes : List UInt8 :=
  [0x4F]

inductive DataFeedIndicator where
  | opra -- Opra
  | unlisted (byte : { byte : UInt8 // byte ∉ DataFeedIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DataFeedIndicator

def toByte : DataFeedIndicator → UInt8
  | .opra => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : DataFeedIndicator :=
  .opra

def ofByte (byte : UInt8) : DataFeedIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DataFeedIndicator) : ofByte value.toByte = value := by
  cases value with
  | opra => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DataFeedIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DataFeedIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DataFeedIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DataFeedIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DataFeedIndicator

/-- Retransmission Indicator: one byte code -/
def RetransmissionIndicator.codes : List UInt8 :=
  [0x20, 0x56]

inductive RetransmissionIndicator where
  | notRetransmitted -- Not Retransmitted
  | retransmitted -- Retransmitted
  | unlisted (byte : { byte : UInt8 // byte ∉ RetransmissionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetransmissionIndicator

def toByte : RetransmissionIndicator → UInt8
  | .notRetransmitted => 0x20
  | .retransmitted => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RetransmissionIndicator :=
  if byte = 0x20 then .notRetransmitted
  else .retransmitted

def ofByte (byte : UInt8) : RetransmissionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetransmissionIndicator) : ofByte value.toByte = value := by
  cases value with
  | notRetransmitted => decide
  | retransmitted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RetransmissionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetransmissionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RetransmissionIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RetransmissionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RetransmissionIndicator

/-- Participant Id: one byte code -/
def ParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x48, 0x49, 0x4A, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x53, 0x54, 0x55, 0x57, 0x58, 0x5A]

inductive ParticipantId where
  | amex -- Amex
  | box -- Box
  | cboe -- Cboe
  | emerald -- Emerald
  | edgx -- Edgx
  | gemx -- Gemx
  | ise -- Ise
  | mrx -- Mrx
  | miax -- Miax
  | nyse -- Nyse
  | opra -- Opra
  | pearl -- Pearl
  | nasd -- Nasd
  | sphr -- Sphr
  | bx -- Bx
  | memx -- Memx
  | c2 -- C 2
  | phlx -- Phlx
  | bats -- Bats
  | unlisted (byte : { byte : UInt8 // byte ∉ ParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ParticipantId

def toByte : ParticipantId → UInt8
  | .amex => 0x41
  | .box => 0x42
  | .cboe => 0x43
  | .emerald => 0x44
  | .edgx => 0x45
  | .gemx => 0x48
  | .ise => 0x49
  | .mrx => 0x4A
  | .miax => 0x4D
  | .nyse => 0x4E
  | .opra => 0x4F
  | .pearl => 0x50
  | .nasd => 0x51
  | .sphr => 0x53
  | .bx => 0x54
  | .memx => 0x55
  | .c2 => 0x57
  | .phlx => 0x58
  | .bats => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ParticipantId :=
  if byte = 0x41 then .amex
  else if byte = 0x42 then .box
  else if byte = 0x43 then .cboe
  else if byte = 0x44 then .emerald
  else if byte = 0x45 then .edgx
  else if byte = 0x48 then .gemx
  else if byte = 0x49 then .ise
  else if byte = 0x4A then .mrx
  else if byte = 0x4D then .miax
  else if byte = 0x4E then .nyse
  else if byte = 0x4F then .opra
  else if byte = 0x50 then .pearl
  else if byte = 0x51 then .nasd
  else if byte = 0x53 then .sphr
  else if byte = 0x54 then .bx
  else if byte = 0x55 then .memx
  else if byte = 0x57 then .c2
  else if byte = 0x58 then .phlx
  else .bats

def ofByte (byte : UInt8) : ParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ParticipantId) : ofByte value.toByte = value := by
  cases value with
  | amex => decide
  | box => decide
  | cboe => decide
  | emerald => decide
  | edgx => decide
  | gemx => decide
  | ise => decide
  | mrx => decide
  | miax => decide
  | nyse => decide
  | opra => decide
  | pearl => decide
  | nasd => decide
  | sphr => decide
  | bx => decide
  | memx => decide
  | c2 => decide
  | phlx => decide
  | bats => decide
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

/-- Expiration Month: one byte code -/
def ExpirationMonth.codes : List UInt8 :=
  [0x41, 0x4D, 0x42, 0x4E, 0x43, 0x4F, 0x44, 0x50, 0x45, 0x51, 0x46, 0x52, 0x47, 0x53, 0x48, 0x54, 0x49, 0x55, 0x4A, 0x56, 0x4B, 0x57, 0x4C, 0x58]

inductive ExpirationMonth where
  | januaryCall -- January Call
  | januaryPut -- January Put
  | februaryCall -- February Call
  | februaryPut -- February Put
  | marchCall -- March Call
  | marchPut -- March Put
  | aprilCall -- April Call
  | aprilPut -- April Put
  | mayCall -- May Call
  | mayPut -- May Put
  | juneCall -- June Call
  | junePut -- June Put
  | julyCall -- July Call
  | julyPut -- July Put
  | augustCall -- August Call
  | augustPut -- August Put
  | septemberCall -- September Call
  | septemberPut -- September Put
  | octoberCall -- October Call
  | octoberPut -- October Put
  | novemberCall -- November Call
  | novemberPut -- November Put
  | decemberCall -- December Call
  | decemberPut -- December Put
  | unlisted (byte : { byte : UInt8 // byte ∉ ExpirationMonth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExpirationMonth

def toByte : ExpirationMonth → UInt8
  | .januaryCall => 0x41
  | .januaryPut => 0x4D
  | .februaryCall => 0x42
  | .februaryPut => 0x4E
  | .marchCall => 0x43
  | .marchPut => 0x4F
  | .aprilCall => 0x44
  | .aprilPut => 0x50
  | .mayCall => 0x45
  | .mayPut => 0x51
  | .juneCall => 0x46
  | .junePut => 0x52
  | .julyCall => 0x47
  | .julyPut => 0x53
  | .augustCall => 0x48
  | .augustPut => 0x54
  | .septemberCall => 0x49
  | .septemberPut => 0x55
  | .octoberCall => 0x4A
  | .octoberPut => 0x56
  | .novemberCall => 0x4B
  | .novemberPut => 0x57
  | .decemberCall => 0x4C
  | .decemberPut => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExpirationMonth :=
  if byte = 0x41 then .januaryCall
  else if byte = 0x4D then .januaryPut
  else if byte = 0x42 then .februaryCall
  else if byte = 0x4E then .februaryPut
  else if byte = 0x43 then .marchCall
  else if byte = 0x4F then .marchPut
  else if byte = 0x44 then .aprilCall
  else if byte = 0x50 then .aprilPut
  else if byte = 0x45 then .mayCall
  else if byte = 0x51 then .mayPut
  else if byte = 0x46 then .juneCall
  else if byte = 0x52 then .junePut
  else if byte = 0x47 then .julyCall
  else if byte = 0x53 then .julyPut
  else if byte = 0x48 then .augustCall
  else if byte = 0x54 then .augustPut
  else if byte = 0x49 then .septemberCall
  else if byte = 0x55 then .septemberPut
  else if byte = 0x4A then .octoberCall
  else if byte = 0x56 then .octoberPut
  else if byte = 0x4B then .novemberCall
  else if byte = 0x57 then .novemberPut
  else if byte = 0x4C then .decemberCall
  else .decemberPut

def ofByte (byte : UInt8) : ExpirationMonth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExpirationMonth) : ofByte value.toByte = value := by
  cases value with
  | januaryCall => decide
  | januaryPut => decide
  | februaryCall => decide
  | februaryPut => decide
  | marchCall => decide
  | marchPut => decide
  | aprilCall => decide
  | aprilPut => decide
  | mayCall => decide
  | mayPut => decide
  | juneCall => decide
  | junePut => decide
  | julyCall => decide
  | julyPut => decide
  | augustCall => decide
  | augustPut => decide
  | septemberCall => decide
  | septemberPut => decide
  | octoberCall => decide
  | octoberPut => decide
  | novemberCall => decide
  | novemberPut => decide
  | decemberCall => decide
  | decemberPut => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExpirationMonth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExpirationMonth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExpirationMonth) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExpirationMonth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExpirationMonth

/-- Strike Price Denominator Code: one byte code -/
def StrikePriceDenominatorCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x49]

inductive StrikePriceDenominatorCode where
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | noFraction -- No Fraction
  | unlisted (byte : { byte : UInt8 // byte ∉ StrikePriceDenominatorCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrikePriceDenominatorCode

def toByte : StrikePriceDenominatorCode → UInt8
  | .ten => 0x41
  | .hundred => 0x42
  | .thousand => 0x43
  | .tenThousand => 0x44
  | .hundredThousand => 0x45
  | .noFraction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrikePriceDenominatorCode :=
  if byte = 0x41 then .ten
  else if byte = 0x42 then .hundred
  else if byte = 0x43 then .thousand
  else if byte = 0x44 then .tenThousand
  else if byte = 0x45 then .hundredThousand
  else .noFraction

def ofByte (byte : UInt8) : StrikePriceDenominatorCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrikePriceDenominatorCode) : ofByte value.toByte = value := by
  cases value with
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | noFraction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrikePriceDenominatorCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrikePriceDenominatorCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrikePriceDenominatorCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StrikePriceDenominatorCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrikePriceDenominatorCode

/-- Premium Price Denominator Code: one byte code -/
def PremiumPriceDenominatorCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x49]

inductive PremiumPriceDenominatorCode where
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | noFraction -- No Fraction
  | unlisted (byte : { byte : UInt8 // byte ∉ PremiumPriceDenominatorCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PremiumPriceDenominatorCode

def toByte : PremiumPriceDenominatorCode → UInt8
  | .ten => 0x41
  | .hundred => 0x42
  | .thousand => 0x43
  | .tenThousand => 0x44
  | .hundredThousand => 0x45
  | .million => 0x46
  | .tenMillion => 0x47
  | .noFraction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PremiumPriceDenominatorCode :=
  if byte = 0x41 then .ten
  else if byte = 0x42 then .hundred
  else if byte = 0x43 then .thousand
  else if byte = 0x44 then .tenThousand
  else if byte = 0x45 then .hundredThousand
  else if byte = 0x46 then .million
  else if byte = 0x47 then .tenMillion
  else .noFraction

def ofByte (byte : UInt8) : PremiumPriceDenominatorCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PremiumPriceDenominatorCode) : ofByte value.toByte = value := by
  cases value with
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | noFraction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PremiumPriceDenominatorCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PremiumPriceDenominatorCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PremiumPriceDenominatorCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PremiumPriceDenominatorCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PremiumPriceDenominatorCode

/-- Underlying Price Denominator Code: one byte code -/
def UnderlyingPriceDenominatorCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49]

inductive UnderlyingPriceDenominatorCode where
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | noFraction -- No Fraction
  | unlisted (byte : { byte : UInt8 // byte ∉ UnderlyingPriceDenominatorCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UnderlyingPriceDenominatorCode

def toByte : UnderlyingPriceDenominatorCode → UInt8
  | .ten => 0x41
  | .hundred => 0x42
  | .thousand => 0x43
  | .tenThousand => 0x44
  | .hundredThousand => 0x45
  | .million => 0x46
  | .tenMillion => 0x47
  | .hundredMillion => 0x48
  | .noFraction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UnderlyingPriceDenominatorCode :=
  if byte = 0x41 then .ten
  else if byte = 0x42 then .hundred
  else if byte = 0x43 then .thousand
  else if byte = 0x44 then .tenThousand
  else if byte = 0x45 then .hundredThousand
  else if byte = 0x46 then .million
  else if byte = 0x47 then .tenMillion
  else if byte = 0x48 then .hundredMillion
  else .noFraction

def ofByte (byte : UInt8) : UnderlyingPriceDenominatorCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UnderlyingPriceDenominatorCode) : ofByte value.toByte = value := by
  cases value with
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | noFraction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UnderlyingPriceDenominatorCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UnderlyingPriceDenominatorCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UnderlyingPriceDenominatorCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : UnderlyingPriceDenominatorCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UnderlyingPriceDenominatorCode

/-- Best Bid Participant Id: one byte code -/
def BestBidParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x48, 0x49, 0x4A, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x54, 0x57, 0x58, 0x5A]

inductive BestBidParticipantId where
  | nyseAmerican -- Nyse American
  | bostonOptionsExchange -- Boston Options Exchange
  | cboeOptionsExchange -- Cboe Options Exchange
  | miaxEmerald -- Miax Emerald
  | cboeEdgxOptions -- Cboe Edgx Options
  | nasdaqGemx -- Nasdaq Gemx
  | nasdaqIse -- Nasdaq Ise
  | nasdaqMrx -- Nasdaq Mrx
  | miamiInternationalSecuritiesExchange -- Miami International Securities Exchange
  | nyseArca -- Nyse Arca
  | optionsPriceReportingAuthority -- Options Price Reporting Authority
  | miaxPearl -- Miax Pearl
  | nasdaqOptionsMarket -- Nasdaq Options Market
  | nasdaqBxOptions -- Nasdaq Bx Options
  | cboeC2Options -- Cboe C 2 Options
  | nasdaqPhlx -- Nasdaq Phlx
  | cboeBzxOptionsExchange -- Cboe Bzx Options Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ BestBidParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BestBidParticipantId

def toByte : BestBidParticipantId → UInt8
  | .nyseAmerican => 0x41
  | .bostonOptionsExchange => 0x42
  | .cboeOptionsExchange => 0x43
  | .miaxEmerald => 0x44
  | .cboeEdgxOptions => 0x45
  | .nasdaqGemx => 0x48
  | .nasdaqIse => 0x49
  | .nasdaqMrx => 0x4A
  | .miamiInternationalSecuritiesExchange => 0x4D
  | .nyseArca => 0x4E
  | .optionsPriceReportingAuthority => 0x4F
  | .miaxPearl => 0x50
  | .nasdaqOptionsMarket => 0x51
  | .nasdaqBxOptions => 0x54
  | .cboeC2Options => 0x57
  | .nasdaqPhlx => 0x58
  | .cboeBzxOptionsExchange => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BestBidParticipantId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .bostonOptionsExchange
  else if byte = 0x43 then .cboeOptionsExchange
  else if byte = 0x44 then .miaxEmerald
  else if byte = 0x45 then .cboeEdgxOptions
  else if byte = 0x48 then .nasdaqGemx
  else if byte = 0x49 then .nasdaqIse
  else if byte = 0x4A then .nasdaqMrx
  else if byte = 0x4D then .miamiInternationalSecuritiesExchange
  else if byte = 0x4E then .nyseArca
  else if byte = 0x4F then .optionsPriceReportingAuthority
  else if byte = 0x50 then .miaxPearl
  else if byte = 0x51 then .nasdaqOptionsMarket
  else if byte = 0x54 then .nasdaqBxOptions
  else if byte = 0x57 then .cboeC2Options
  else if byte = 0x58 then .nasdaqPhlx
  else .cboeBzxOptionsExchange

def ofByte (byte : UInt8) : BestBidParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BestBidParticipantId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | bostonOptionsExchange => decide
  | cboeOptionsExchange => decide
  | miaxEmerald => decide
  | cboeEdgxOptions => decide
  | nasdaqGemx => decide
  | nasdaqIse => decide
  | nasdaqMrx => decide
  | miamiInternationalSecuritiesExchange => decide
  | nyseArca => decide
  | optionsPriceReportingAuthority => decide
  | miaxPearl => decide
  | nasdaqOptionsMarket => decide
  | nasdaqBxOptions => decide
  | cboeC2Options => decide
  | nasdaqPhlx => decide
  | cboeBzxOptionsExchange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BestBidParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BestBidParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BestBidParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BestBidParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BestBidParticipantId

/-- Best Bid Denominator Code: one byte code -/
def BestBidDenominatorCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49]

inductive BestBidDenominatorCode where
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | noFraction -- No Fraction
  | unlisted (byte : { byte : UInt8 // byte ∉ BestBidDenominatorCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BestBidDenominatorCode

def toByte : BestBidDenominatorCode → UInt8
  | .ten => 0x41
  | .hundred => 0x42
  | .thousand => 0x43
  | .tenThousand => 0x44
  | .hundredThousand => 0x45
  | .million => 0x46
  | .tenMillion => 0x47
  | .hundredMillion => 0x48
  | .noFraction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BestBidDenominatorCode :=
  if byte = 0x41 then .ten
  else if byte = 0x42 then .hundred
  else if byte = 0x43 then .thousand
  else if byte = 0x44 then .tenThousand
  else if byte = 0x45 then .hundredThousand
  else if byte = 0x46 then .million
  else if byte = 0x47 then .tenMillion
  else if byte = 0x48 then .hundredMillion
  else .noFraction

def ofByte (byte : UInt8) : BestBidDenominatorCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BestBidDenominatorCode) : ofByte value.toByte = value := by
  cases value with
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | noFraction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BestBidDenominatorCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BestBidDenominatorCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BestBidDenominatorCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BestBidDenominatorCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BestBidDenominatorCode

/-- Best Offer Participant Id: one byte code -/
def BestOfferParticipantId.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x48, 0x49, 0x4A, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x54, 0x57, 0x58, 0x5A]

inductive BestOfferParticipantId where
  | nyseAmerican -- Nyse American
  | bostonOptionsExchange -- Boston Options Exchange
  | cboeOptionsExchange -- Cboe Options Exchange
  | miaxEmerald -- Miax Emerald
  | cboeEdgxOptions -- Cboe Edgx Options
  | nasdaqGemx -- Nasdaq Gemx
  | nasdaqIse -- Nasdaq Ise
  | nasdaqMrx -- Nasdaq Mrx
  | miamiInternationalSecuritiesExchange -- Miami International Securities Exchange
  | nyseArca -- Nyse Arca
  | optionsPriceReportingAuthority -- Options Price Reporting Authority
  | miaxPearl -- Miax Pearl
  | nasdaqOptionsMarket -- Nasdaq Options Market
  | nasdaqBxOptions -- Nasdaq Bx Options
  | cboeC2Options -- Cboe C 2 Options
  | nasdaqPhlx -- Nasdaq Phlx
  | cboeBzxOptionsExchange -- Cboe Bzx Options Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ BestOfferParticipantId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BestOfferParticipantId

def toByte : BestOfferParticipantId → UInt8
  | .nyseAmerican => 0x41
  | .bostonOptionsExchange => 0x42
  | .cboeOptionsExchange => 0x43
  | .miaxEmerald => 0x44
  | .cboeEdgxOptions => 0x45
  | .nasdaqGemx => 0x48
  | .nasdaqIse => 0x49
  | .nasdaqMrx => 0x4A
  | .miamiInternationalSecuritiesExchange => 0x4D
  | .nyseArca => 0x4E
  | .optionsPriceReportingAuthority => 0x4F
  | .miaxPearl => 0x50
  | .nasdaqOptionsMarket => 0x51
  | .nasdaqBxOptions => 0x54
  | .cboeC2Options => 0x57
  | .nasdaqPhlx => 0x58
  | .cboeBzxOptionsExchange => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BestOfferParticipantId :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .bostonOptionsExchange
  else if byte = 0x43 then .cboeOptionsExchange
  else if byte = 0x44 then .miaxEmerald
  else if byte = 0x45 then .cboeEdgxOptions
  else if byte = 0x48 then .nasdaqGemx
  else if byte = 0x49 then .nasdaqIse
  else if byte = 0x4A then .nasdaqMrx
  else if byte = 0x4D then .miamiInternationalSecuritiesExchange
  else if byte = 0x4E then .nyseArca
  else if byte = 0x4F then .optionsPriceReportingAuthority
  else if byte = 0x50 then .miaxPearl
  else if byte = 0x51 then .nasdaqOptionsMarket
  else if byte = 0x54 then .nasdaqBxOptions
  else if byte = 0x57 then .cboeC2Options
  else if byte = 0x58 then .nasdaqPhlx
  else .cboeBzxOptionsExchange

def ofByte (byte : UInt8) : BestOfferParticipantId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BestOfferParticipantId) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | bostonOptionsExchange => decide
  | cboeOptionsExchange => decide
  | miaxEmerald => decide
  | cboeEdgxOptions => decide
  | nasdaqGemx => decide
  | nasdaqIse => decide
  | nasdaqMrx => decide
  | miamiInternationalSecuritiesExchange => decide
  | nyseArca => decide
  | optionsPriceReportingAuthority => decide
  | miaxPearl => decide
  | nasdaqOptionsMarket => decide
  | nasdaqBxOptions => decide
  | cboeC2Options => decide
  | nasdaqPhlx => decide
  | cboeBzxOptionsExchange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BestOfferParticipantId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BestOfferParticipantId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BestOfferParticipantId) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BestOfferParticipantId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BestOfferParticipantId

/-- Best Offer Denominator Code: one byte code -/
def BestOfferDenominatorCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49]

inductive BestOfferDenominatorCode where
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | noFraction -- No Fraction
  | unlisted (byte : { byte : UInt8 // byte ∉ BestOfferDenominatorCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BestOfferDenominatorCode

def toByte : BestOfferDenominatorCode → UInt8
  | .ten => 0x41
  | .hundred => 0x42
  | .thousand => 0x43
  | .tenThousand => 0x44
  | .hundredThousand => 0x45
  | .million => 0x46
  | .tenMillion => 0x47
  | .hundredMillion => 0x48
  | .noFraction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BestOfferDenominatorCode :=
  if byte = 0x41 then .ten
  else if byte = 0x42 then .hundred
  else if byte = 0x43 then .thousand
  else if byte = 0x44 then .tenThousand
  else if byte = 0x45 then .hundredThousand
  else if byte = 0x46 then .million
  else if byte = 0x47 then .tenMillion
  else if byte = 0x48 then .hundredMillion
  else .noFraction

def ofByte (byte : UInt8) : BestOfferDenominatorCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BestOfferDenominatorCode) : ofByte value.toByte = value := by
  cases value with
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | noFraction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BestOfferDenominatorCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BestOfferDenominatorCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BestOfferDenominatorCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BestOfferDenominatorCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BestOfferDenominatorCode

/-- Index Value Denominator Code: one byte code -/
def IndexValueDenominatorCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x49]

inductive IndexValueDenominatorCode where
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | noFraction -- No Fraction
  | unlisted (byte : { byte : UInt8 // byte ∉ IndexValueDenominatorCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IndexValueDenominatorCode

def toByte : IndexValueDenominatorCode → UInt8
  | .ten => 0x41
  | .hundred => 0x42
  | .thousand => 0x43
  | .tenThousand => 0x44
  | .hundredThousand => 0x45
  | .million => 0x46
  | .tenMillion => 0x47
  | .noFraction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IndexValueDenominatorCode :=
  if byte = 0x41 then .ten
  else if byte = 0x42 then .hundred
  else if byte = 0x43 then .thousand
  else if byte = 0x44 then .tenThousand
  else if byte = 0x45 then .hundredThousand
  else if byte = 0x46 then .million
  else if byte = 0x47 then .tenMillion
  else .noFraction

def ofByte (byte : UInt8) : IndexValueDenominatorCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IndexValueDenominatorCode) : ofByte value.toByte = value := by
  cases value with
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | noFraction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IndexValueDenominatorCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IndexValueDenominatorCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IndexValueDenominatorCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : IndexValueDenominatorCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IndexValueDenominatorCode

/-- Block Timestamp: 8 bytes -/
structure BlockTimestamp where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace BlockTimestamp

def encode (message : BlockTimestamp) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (BlockTimestamp × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : BlockTimestamp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BlockTimestamp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BlockTimestamp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BlockTimestamp

/-- Administrative Message -/
structure AdministrativeMessage where
  messageIndicator : Alpha 1
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 32
  messageData : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace AdministrativeMessage

def encode (message : AdministrativeMessage) : List UInt8 :=
  Alpha.encode message.messageIndicator
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.messageData.val.length)
    ++ (encodeMany Byte.encode message.messageData.val))))

def decode (bytes : List UInt8) : Option (AdministrativeMessage × List UInt8) := do
  let (messageIndicator, bytes) ← Alpha.decode 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (messageDataLength, bytes) ← decodeUInt 2 bytes
  let (messageData_, bytes) ← decodeMany Byte.decode messageDataLength.toNat bytes
  if fits_messageData : messageData_.length < 256 ^ 2 then
    pure ({ messageIndicator, transactionId, participantReferenceNumber, messageData := ⟨messageData_, fits_messageData⟩ }, bytes)
  else none

theorem encode_length_pos (message : AdministrativeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AdministrativeMessage) : (encode message).length ≤ 65546 := by
  have bound_messageData := message.messageData.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : AdministrativeMessage) (rest : List UInt8) :
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
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.messageData.length_lt]
  rfl

end AdministrativeMessage

/-- Any Administrative Message Payload, selected by Administrative Message Type -/
inductive AdministrativeMessagePayload where
  | administrativeMessage (message : AdministrativeMessage) -- " " 0x20
  deriving DecidableEq, Repr

namespace AdministrativeMessagePayload

/-- The Administrative Message Type each message is sent under -/
def tag : AdministrativeMessagePayload → BitVec 8
  | .administrativeMessage _ => 32

def encode : AdministrativeMessagePayload → List UInt8
  | .administrativeMessage message => AdministrativeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AdministrativeMessagePayload) : (encode message).length ≤ 65546 := by
  cases message with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AdministrativeMessagePayload × List UInt8) :=
  if tag = 32 then (AdministrativeMessage.decode bytes).map fun (message, rest) => (.administrativeMessage message, rest)
  else none

@[simp] theorem decode_encode (message : AdministrativeMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end AdministrativeMessagePayload

/-- Administrative Category -/
structure AdministrativeCategory where
  administrativeMessagePayload : AdministrativeMessagePayload
  deriving DecidableEq, Repr

namespace AdministrativeCategory

def encode (message : AdministrativeCategory) : List UInt8 :=
  encodeUInt 1 (AdministrativeMessagePayload.tag message.administrativeMessagePayload)
    ++ (AdministrativeMessagePayload.encode message.administrativeMessagePayload)

def decode (bytes : List UInt8) : Option (AdministrativeCategory × List UInt8) := do
  let (administrativeMessageType, bytes) ← decodeUInt 1 bytes
  let (administrativeMessagePayload, bytes) ← AdministrativeMessagePayload.decode administrativeMessageType bytes
  pure ({ administrativeMessagePayload }, bytes)

theorem encode_length_pos (message : AdministrativeCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AdministrativeCategory) : (encode message).length ≤ 65547 := by
  unfold encode
  cases message.administrativeMessagePayload with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : AdministrativeCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [AdministrativeMessagePayload.decode_encode, some_bind]
  rfl

end AdministrativeCategory

/-- Control Message: 9 bytes -/
structure ControlMessage where
  messageIndicator : Alpha 1
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 32
  deriving DecidableEq, Repr

namespace ControlMessage

def encode (message : ControlMessage) : List UInt8 :=
  Alpha.encode message.messageIndicator
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 4 message.participantReferenceNumber))

def decode (bytes : List UInt8) : Option (ControlMessage × List UInt8) := do
  let (messageIndicator, bytes) ← Alpha.decode 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  pure ({ messageIndicator, transactionId, participantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : ControlMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ControlMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ControlMessage

/-- Any Control Message Payload, selected by Control Message Type -/
inductive ControlMessagePayload where
  | controlMessage (message : ControlMessage) -- "C" 0x43
  deriving DecidableEq, Repr

namespace ControlMessagePayload

/-- The Control Message Type each message is sent under -/
def tag : ControlMessagePayload → BitVec 8
  | .controlMessage _ => 67

def encode : ControlMessagePayload → List UInt8
  | .controlMessage message => ControlMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ControlMessagePayload) : (encode message).length ≤ 9 := by
  cases message with
  | controlMessage inner =>
    simp only [encode, ControlMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ControlMessagePayload × List UInt8) :=
  if tag = 67 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ControlMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ControlMessagePayload

/-- Control Category -/
structure ControlCategory where
  controlMessagePayload : ControlMessagePayload
  deriving DecidableEq, Repr

namespace ControlCategory

def encode (message : ControlCategory) : List UInt8 :=
  encodeUInt 1 (ControlMessagePayload.tag message.controlMessagePayload)
    ++ (ControlMessagePayload.encode message.controlMessagePayload)

def decode (bytes : List UInt8) : Option (ControlCategory × List UInt8) := do
  let (controlMessageType, bytes) ← decodeUInt 1 bytes
  let (controlMessagePayload, bytes) ← ControlMessagePayload.decode controlMessageType bytes
  pure ({ controlMessagePayload }, bytes)

theorem encode_length_pos (message : ControlCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ControlCategory) : (encode message).length ≤ 10 := by
  unfold encode
  cases message.controlMessagePayload with
  | controlMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, ControlMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ControlCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ControlMessagePayload.decode_encode, some_bind]
  rfl

end ControlCategory

/-- Expiration Block: 3 bytes -/
structure ExpirationBlock where
  expirationMonth : ExpirationMonth
  expirationDay : BitVec 8
  expirationYear : BitVec 8
  deriving DecidableEq, Repr

namespace ExpirationBlock

def encode (message : ExpirationBlock) : List UInt8 :=
  ExpirationMonth.encode message.expirationMonth
    ++ (encodeUInt 1 message.expirationDay
    ++ (encodeUInt 1 message.expirationYear))

def decode (bytes : List UInt8) : Option (ExpirationBlock × List UInt8) := do
  let (expirationMonth, bytes) ← ExpirationMonth.decode bytes
  let (expirationDay, bytes) ← decodeUInt 1 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  pure ({ expirationMonth, expirationDay, expirationYear }, bytes)

@[simp] theorem encode_length (message : ExpirationBlock) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, ExpirationMonth.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ExpirationBlock) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExpirationBlock) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ExpirationMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExpirationBlock

/-- Equity And Index Last Sale Message: 40 bytes -/
structure EquityAndIndexLastSaleMessage where
  messageIndicator : Alpha 1
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 32
  securitySymbol : Alpha 5
  reserved1 : Alpha 1
  expirationBlock : ExpirationBlock
  strikePriceDenominatorCode : StrikePriceDenominatorCode
  strikePrice : BitVec 32
  volume : BitVec 32
  premiumPriceDenominatorCode : PremiumPriceDenominatorCode
  premiumPrice : BitVec 32
  tradeIdentifier : BitVec 32
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace EquityAndIndexLastSaleMessage

def encode (message : EquityAndIndexLastSaleMessage) : List UInt8 :=
  Alpha.encode message.messageIndicator
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.reserved1
    ++ (ExpirationBlock.encode message.expirationBlock
    ++ (StrikePriceDenominatorCode.encode message.strikePriceDenominatorCode
    ++ (encodeUInt 4 message.strikePrice
    ++ (encodeUInt 4 message.volume
    ++ (PremiumPriceDenominatorCode.encode message.premiumPriceDenominatorCode
    ++ (encodeUInt 4 message.premiumPrice
    ++ (encodeUInt 4 message.tradeIdentifier
    ++ (Alpha.encode message.reserved4))))))))))))

def decode (bytes : List UInt8) : Option (EquityAndIndexLastSaleMessage × List UInt8) := do
  let (messageIndicator, bytes) ← Alpha.decode 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (expirationBlock, bytes) ← ExpirationBlock.decode bytes
  let (strikePriceDenominatorCode, bytes) ← StrikePriceDenominatorCode.decode bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (premiumPriceDenominatorCode, bytes) ← PremiumPriceDenominatorCode.decode bytes
  let (premiumPrice, bytes) ← decodeUInt 4 bytes
  let (tradeIdentifier, bytes) ← decodeUInt 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ messageIndicator, transactionId, participantReferenceNumber, securitySymbol, reserved1, expirationBlock, strikePriceDenominatorCode, strikePrice, volume, premiumPriceDenominatorCode, premiumPrice, tradeIdentifier, reserved4 }, bytes)

@[simp] theorem encode_length (message : EquityAndIndexLastSaleMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length]

theorem encode_length_pos (message : EquityAndIndexLastSaleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquityAndIndexLastSaleMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpirationBlock.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PremiumPriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EquityAndIndexLastSaleMessage

/-- Any Equity And Index Last Sale Message Payload, selected by Equity And Index Last Sale Message Type -/
inductive EquityAndIndexLastSaleMessagePayload where
  | equityAndIndexLastSaleMessage (message : EquityAndIndexLastSaleMessage) -- "A" 0x41
  deriving DecidableEq, Repr

namespace EquityAndIndexLastSaleMessagePayload

/-- The Equity And Index Last Sale Message Type each message is sent under -/
def tag : EquityAndIndexLastSaleMessagePayload → BitVec 8
  | .equityAndIndexLastSaleMessage _ => 65

def encode : EquityAndIndexLastSaleMessagePayload → List UInt8
  | .equityAndIndexLastSaleMessage message => EquityAndIndexLastSaleMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : EquityAndIndexLastSaleMessagePayload) : (encode message).length ≤ 40 := by
  cases message with
  | equityAndIndexLastSaleMessage inner =>
    simp only [encode, EquityAndIndexLastSaleMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (EquityAndIndexLastSaleMessagePayload × List UInt8) :=
  if tag = 65 then (EquityAndIndexLastSaleMessage.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleMessage message, rest)
  else none

@[simp] theorem decode_encode (message : EquityAndIndexLastSaleMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end EquityAndIndexLastSaleMessagePayload

/-- Equity And Index Last Sale Category -/
structure EquityAndIndexLastSaleCategory where
  equityAndIndexLastSaleMessagePayload : EquityAndIndexLastSaleMessagePayload
  deriving DecidableEq, Repr

namespace EquityAndIndexLastSaleCategory

def encode (message : EquityAndIndexLastSaleCategory) : List UInt8 :=
  encodeUInt 1 (EquityAndIndexLastSaleMessagePayload.tag message.equityAndIndexLastSaleMessagePayload)
    ++ (EquityAndIndexLastSaleMessagePayload.encode message.equityAndIndexLastSaleMessagePayload)

def decode (bytes : List UInt8) : Option (EquityAndIndexLastSaleCategory × List UInt8) := do
  let (equityAndIndexLastSaleMessageType, bytes) ← decodeUInt 1 bytes
  let (equityAndIndexLastSaleMessagePayload, bytes) ← EquityAndIndexLastSaleMessagePayload.decode equityAndIndexLastSaleMessageType bytes
  pure ({ equityAndIndexLastSaleMessagePayload }, bytes)

theorem encode_length_pos (message : EquityAndIndexLastSaleCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EquityAndIndexLastSaleCategory) : (encode message).length ≤ 41 := by
  unfold encode
  cases message.equityAndIndexLastSaleMessagePayload with
  | equityAndIndexLastSaleMessage inner =>
    simp only [EquityAndIndexLastSaleMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexLastSaleMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : EquityAndIndexLastSaleCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EquityAndIndexLastSaleMessagePayload.decode_encode, some_bind]
  rfl

end EquityAndIndexLastSaleCategory

/-- Open Interest Message: 27 bytes -/
structure OpenInterestMessage where
  messageIndicator : Alpha 1
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 32
  securitySymbol : Alpha 5
  reserved1 : Alpha 1
  expirationBlock : ExpirationBlock
  strikePriceDenominatorCode : StrikePriceDenominatorCode
  strikePrice : BitVec 32
  openInterestVolume : BitVec 32
  deriving DecidableEq, Repr

namespace OpenInterestMessage

def encode (message : OpenInterestMessage) : List UInt8 :=
  Alpha.encode message.messageIndicator
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.reserved1
    ++ (ExpirationBlock.encode message.expirationBlock
    ++ (StrikePriceDenominatorCode.encode message.strikePriceDenominatorCode
    ++ (encodeUInt 4 message.strikePrice
    ++ (encodeUInt 4 message.openInterestVolume))))))))

def decode (bytes : List UInt8) : Option (OpenInterestMessage × List UInt8) := do
  let (messageIndicator, bytes) ← Alpha.decode 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (expirationBlock, bytes) ← ExpirationBlock.decode bytes
  let (strikePriceDenominatorCode, bytes) ← StrikePriceDenominatorCode.decode bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (openInterestVolume, bytes) ← decodeUInt 4 bytes
  pure ({ messageIndicator, transactionId, participantReferenceNumber, securitySymbol, reserved1, expirationBlock, strikePriceDenominatorCode, strikePrice, openInterestVolume }, bytes)

@[simp] theorem encode_length (message : OpenInterestMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length]

theorem encode_length_pos (message : OpenInterestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenInterestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpirationBlock.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpenInterestMessage

/-- Any Open Interest Message Payload, selected by Open Interest Message Type -/
inductive OpenInterestMessagePayload where
  | openInterestMessage (message : OpenInterestMessage) -- " " 0x20
  deriving DecidableEq, Repr

namespace OpenInterestMessagePayload

/-- The Open Interest Message Type each message is sent under -/
def tag : OpenInterestMessagePayload → BitVec 8
  | .openInterestMessage _ => 32

def encode : OpenInterestMessagePayload → List UInt8
  | .openInterestMessage message => OpenInterestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : OpenInterestMessagePayload) : (encode message).length ≤ 27 := by
  cases message with
  | openInterestMessage inner =>
    simp only [encode, OpenInterestMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (OpenInterestMessagePayload × List UInt8) :=
  if tag = 32 then (OpenInterestMessage.decode bytes).map fun (message, rest) => (.openInterestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : OpenInterestMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end OpenInterestMessagePayload

/-- Open Interest Category -/
structure OpenInterestCategory where
  openInterestMessagePayload : OpenInterestMessagePayload
  deriving DecidableEq, Repr

namespace OpenInterestCategory

def encode (message : OpenInterestCategory) : List UInt8 :=
  encodeUInt 1 (OpenInterestMessagePayload.tag message.openInterestMessagePayload)
    ++ (OpenInterestMessagePayload.encode message.openInterestMessagePayload)

def decode (bytes : List UInt8) : Option (OpenInterestCategory × List UInt8) := do
  let (openInterestMessageType, bytes) ← decodeUInt 1 bytes
  let (openInterestMessagePayload, bytes) ← OpenInterestMessagePayload.decode openInterestMessageType bytes
  pure ({ openInterestMessagePayload }, bytes)

theorem encode_length_pos (message : OpenInterestCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OpenInterestCategory) : (encode message).length ≤ 28 := by
  unfold encode
  cases message.openInterestMessagePayload with
  | openInterestMessage inner =>
    simp only [OpenInterestMessagePayload.encode, List.length_append, encodeUInt_length, OpenInterestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : OpenInterestCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OpenInterestMessagePayload.decode_encode, some_bind]
  rfl

end OpenInterestCategory

/-- Equity And Index End Of Day Summary Message: 69 bytes -/
structure EquityAndIndexEndOfDaySummaryMessage where
  messageIndicator : Alpha 1
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 32
  securitySymbol : Alpha 5
  reserved1 : Alpha 1
  expirationBlock : ExpirationBlock
  strikePriceDenominatorCode : StrikePriceDenominatorCode
  strikePrice : BitVec 32
  volume : BitVec 32
  openInterestVolume : BitVec 32
  premiumPriceDenominatorCode : PremiumPriceDenominatorCode
  openPrice : BitVec 32
  highPrice : BitVec 32
  lowPrice : BitVec 32
  lastPrice : BitVec 32
  netChange : BitVec 32
  underlyingPriceDenominatorCode : UnderlyingPriceDenominatorCode
  underlyingPrice : BitVec 64
  bidPrice : BitVec 32
  offerPrice : BitVec 32
  deriving DecidableEq, Repr

namespace EquityAndIndexEndOfDaySummaryMessage

def encode (message : EquityAndIndexEndOfDaySummaryMessage) : List UInt8 :=
  Alpha.encode message.messageIndicator
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.reserved1
    ++ (ExpirationBlock.encode message.expirationBlock
    ++ (StrikePriceDenominatorCode.encode message.strikePriceDenominatorCode
    ++ (encodeUInt 4 message.strikePrice
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.openInterestVolume
    ++ (PremiumPriceDenominatorCode.encode message.premiumPriceDenominatorCode
    ++ (encodeUInt 4 message.openPrice
    ++ (encodeUInt 4 message.highPrice
    ++ (encodeUInt 4 message.lowPrice
    ++ (encodeUInt 4 message.lastPrice
    ++ (encodeUInt 4 message.netChange
    ++ (UnderlyingPriceDenominatorCode.encode message.underlyingPriceDenominatorCode
    ++ (encodeUInt 8 message.underlyingPrice
    ++ (encodeUInt 4 message.bidPrice
    ++ (encodeUInt 4 message.offerPrice)))))))))))))))))))

def decode (bytes : List UInt8) : Option (EquityAndIndexEndOfDaySummaryMessage × List UInt8) := do
  let (messageIndicator, bytes) ← Alpha.decode 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (expirationBlock, bytes) ← ExpirationBlock.decode bytes
  let (strikePriceDenominatorCode, bytes) ← StrikePriceDenominatorCode.decode bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (openInterestVolume, bytes) ← decodeUInt 4 bytes
  let (premiumPriceDenominatorCode, bytes) ← PremiumPriceDenominatorCode.decode bytes
  let (openPrice, bytes) ← decodeUInt 4 bytes
  let (highPrice, bytes) ← decodeUInt 4 bytes
  let (lowPrice, bytes) ← decodeUInt 4 bytes
  let (lastPrice, bytes) ← decodeUInt 4 bytes
  let (netChange, bytes) ← decodeUInt 4 bytes
  let (underlyingPriceDenominatorCode, bytes) ← UnderlyingPriceDenominatorCode.decode bytes
  let (underlyingPrice, bytes) ← decodeUInt 8 bytes
  let (bidPrice, bytes) ← decodeUInt 4 bytes
  let (offerPrice, bytes) ← decodeUInt 4 bytes
  pure ({ messageIndicator, transactionId, participantReferenceNumber, securitySymbol, reserved1, expirationBlock, strikePriceDenominatorCode, strikePrice, volume, openInterestVolume, premiumPriceDenominatorCode, openPrice, highPrice, lowPrice, lastPrice, netChange, underlyingPriceDenominatorCode, underlyingPrice, bidPrice, offerPrice }, bytes)

@[simp] theorem encode_length (message : EquityAndIndexEndOfDaySummaryMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, UnderlyingPriceDenominatorCode.encode_length]

theorem encode_length_pos (message : EquityAndIndexEndOfDaySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquityAndIndexEndOfDaySummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpirationBlock.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PremiumPriceDenominatorCode.decode_encode, some_bind]
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
  rw [List.append_assoc, UnderlyingPriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EquityAndIndexEndOfDaySummaryMessage

/-- Any Equity And Index End Of Day Summary Message Payload, selected by Equity And Index End Of Day Summary Message Type -/
inductive EquityAndIndexEndOfDaySummaryMessagePayload where
  | equityAndIndexEndOfDaySummaryMessage (message : EquityAndIndexEndOfDaySummaryMessage) -- " " 0x20
  deriving DecidableEq, Repr

namespace EquityAndIndexEndOfDaySummaryMessagePayload

/-- The Equity And Index End Of Day Summary Message Type each message is sent under -/
def tag : EquityAndIndexEndOfDaySummaryMessagePayload → BitVec 8
  | .equityAndIndexEndOfDaySummaryMessage _ => 32

def encode : EquityAndIndexEndOfDaySummaryMessagePayload → List UInt8
  | .equityAndIndexEndOfDaySummaryMessage message => EquityAndIndexEndOfDaySummaryMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : EquityAndIndexEndOfDaySummaryMessagePayload) : (encode message).length ≤ 69 := by
  cases message with
  | equityAndIndexEndOfDaySummaryMessage inner =>
    simp only [encode, EquityAndIndexEndOfDaySummaryMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (EquityAndIndexEndOfDaySummaryMessagePayload × List UInt8) :=
  if tag = 32 then (EquityAndIndexEndOfDaySummaryMessage.decode bytes).map fun (message, rest) => (.equityAndIndexEndOfDaySummaryMessage message, rest)
  else none

@[simp] theorem decode_encode (message : EquityAndIndexEndOfDaySummaryMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end EquityAndIndexEndOfDaySummaryMessagePayload

/-- Equity And Index End Of Day Summary Category -/
structure EquityAndIndexEndOfDaySummaryCategory where
  equityAndIndexEndOfDaySummaryMessagePayload : EquityAndIndexEndOfDaySummaryMessagePayload
  deriving DecidableEq, Repr

namespace EquityAndIndexEndOfDaySummaryCategory

def encode (message : EquityAndIndexEndOfDaySummaryCategory) : List UInt8 :=
  encodeUInt 1 (EquityAndIndexEndOfDaySummaryMessagePayload.tag message.equityAndIndexEndOfDaySummaryMessagePayload)
    ++ (EquityAndIndexEndOfDaySummaryMessagePayload.encode message.equityAndIndexEndOfDaySummaryMessagePayload)

def decode (bytes : List UInt8) : Option (EquityAndIndexEndOfDaySummaryCategory × List UInt8) := do
  let (equityAndIndexEndOfDaySummaryMessageType, bytes) ← decodeUInt 1 bytes
  let (equityAndIndexEndOfDaySummaryMessagePayload, bytes) ← EquityAndIndexEndOfDaySummaryMessagePayload.decode equityAndIndexEndOfDaySummaryMessageType bytes
  pure ({ equityAndIndexEndOfDaySummaryMessagePayload }, bytes)

theorem encode_length_pos (message : EquityAndIndexEndOfDaySummaryCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EquityAndIndexEndOfDaySummaryCategory) : (encode message).length ≤ 70 := by
  unfold encode
  cases message.equityAndIndexEndOfDaySummaryMessagePayload with
  | equityAndIndexEndOfDaySummaryMessage inner =>
    simp only [EquityAndIndexEndOfDaySummaryMessagePayload.encode, List.length_append, encodeUInt_length, EquityAndIndexEndOfDaySummaryMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : EquityAndIndexEndOfDaySummaryCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EquityAndIndexEndOfDaySummaryMessagePayload.decode_encode, some_bind]
  rfl

end EquityAndIndexEndOfDaySummaryCategory

/-- Best Bid Appendage: 10 bytes -/
structure BestBidAppendage where
  bestBidParticipantId : BestBidParticipantId
  bestBidDenominatorCode : BestBidDenominatorCode
  bestBidPrice : BitVec 32
  bestBidSize : BitVec 32
  deriving DecidableEq, Repr

namespace BestBidAppendage

def encode (message : BestBidAppendage) : List UInt8 :=
  BestBidParticipantId.encode message.bestBidParticipantId
    ++ (BestBidDenominatorCode.encode message.bestBidDenominatorCode
    ++ (encodeUInt 4 message.bestBidPrice
    ++ (encodeUInt 4 message.bestBidSize)))

def decode (bytes : List UInt8) : Option (BestBidAppendage × List UInt8) := do
  let (bestBidParticipantId, bytes) ← BestBidParticipantId.decode bytes
  let (bestBidDenominatorCode, bytes) ← BestBidDenominatorCode.decode bytes
  let (bestBidPrice, bytes) ← decodeUInt 4 bytes
  let (bestBidSize, bytes) ← decodeUInt 4 bytes
  pure ({ bestBidParticipantId, bestBidDenominatorCode, bestBidPrice, bestBidSize }, bytes)

@[simp] theorem encode_length (message : BestBidAppendage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, BestBidParticipantId.encode_length, BestBidDenominatorCode.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BestBidAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestBidAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, BestBidParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BestBidDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BestBidAppendage

/-- Best Offer Appendage: 10 bytes -/
structure BestOfferAppendage where
  bestOfferParticipantId : BestOfferParticipantId
  bestOfferDenominatorCode : BestOfferDenominatorCode
  bestOfferPrice : BitVec 32
  bestOfferSize : BitVec 32
  deriving DecidableEq, Repr

namespace BestOfferAppendage

def encode (message : BestOfferAppendage) : List UInt8 :=
  BestOfferParticipantId.encode message.bestOfferParticipantId
    ++ (BestOfferDenominatorCode.encode message.bestOfferDenominatorCode
    ++ (encodeUInt 4 message.bestOfferPrice
    ++ (encodeUInt 4 message.bestOfferSize)))

def decode (bytes : List UInt8) : Option (BestOfferAppendage × List UInt8) := do
  let (bestOfferParticipantId, bytes) ← BestOfferParticipantId.decode bytes
  let (bestOfferDenominatorCode, bytes) ← BestOfferDenominatorCode.decode bytes
  let (bestOfferPrice, bytes) ← decodeUInt 4 bytes
  let (bestOfferSize, bytes) ← decodeUInt 4 bytes
  pure ({ bestOfferParticipantId, bestOfferDenominatorCode, bestOfferPrice, bestOfferSize }, bytes)

@[simp] theorem encode_length (message : BestOfferAppendage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, BestOfferParticipantId.encode_length, BestOfferDenominatorCode.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BestOfferAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestOfferAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, BestOfferParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BestOfferDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BestOfferAppendage

/-- Best Bid And Offer Appendage: 20 bytes -/
structure BestBidAndOfferAppendage where
  bestBidParticipantId : BestBidParticipantId
  bestBidDenominatorCode : BestBidDenominatorCode
  bestBidPrice : BitVec 32
  bestBidSize : BitVec 32
  bestOfferParticipantId : BestOfferParticipantId
  bestOfferDenominatorCode : BestOfferDenominatorCode
  bestOfferPrice : BitVec 32
  bestOfferSize : BitVec 32
  deriving DecidableEq, Repr

namespace BestBidAndOfferAppendage

def encode (message : BestBidAndOfferAppendage) : List UInt8 :=
  BestBidParticipantId.encode message.bestBidParticipantId
    ++ (BestBidDenominatorCode.encode message.bestBidDenominatorCode
    ++ (encodeUInt 4 message.bestBidPrice
    ++ (encodeUInt 4 message.bestBidSize
    ++ (BestOfferParticipantId.encode message.bestOfferParticipantId
    ++ (BestOfferDenominatorCode.encode message.bestOfferDenominatorCode
    ++ (encodeUInt 4 message.bestOfferPrice
    ++ (encodeUInt 4 message.bestOfferSize)))))))

def decode (bytes : List UInt8) : Option (BestBidAndOfferAppendage × List UInt8) := do
  let (bestBidParticipantId, bytes) ← BestBidParticipantId.decode bytes
  let (bestBidDenominatorCode, bytes) ← BestBidDenominatorCode.decode bytes
  let (bestBidPrice, bytes) ← decodeUInt 4 bytes
  let (bestBidSize, bytes) ← decodeUInt 4 bytes
  let (bestOfferParticipantId, bytes) ← BestOfferParticipantId.decode bytes
  let (bestOfferDenominatorCode, bytes) ← BestOfferDenominatorCode.decode bytes
  let (bestOfferPrice, bytes) ← decodeUInt 4 bytes
  let (bestOfferSize, bytes) ← decodeUInt 4 bytes
  pure ({ bestBidParticipantId, bestBidDenominatorCode, bestBidPrice, bestBidSize, bestOfferParticipantId, bestOfferDenominatorCode, bestOfferPrice, bestOfferSize }, bytes)

@[simp] theorem encode_length (message : BestBidAndOfferAppendage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, BestBidParticipantId.encode_length, BestBidDenominatorCode.encode_length, encodeUInt_length, BestOfferParticipantId.encode_length, BestOfferDenominatorCode.encode_length]

theorem encode_length_pos (message : BestBidAndOfferAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestBidAndOfferAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, BestBidParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BestBidDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BestOfferParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BestOfferDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BestBidAndOfferAppendage

/-- Bbo Indicator: 0 bytes -/
structure BboAbsent where
  deriving DecidableEq, Repr

namespace BboAbsent

def encode (_ : BboAbsent) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (BboAbsent × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : BboAbsent) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : BboAbsent) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end BboAbsent

/-- The Best Bid Appendage or Best Offer Appendage or Best Bid And Offer Appendage the Bbo Indicator says is attached, or none -/
inductive BboChoice where
  | bestBidAppendage (message : BestBidAppendage) -- "M" 0x4D
  | bestOfferAppendage (message : BestOfferAppendage) -- "C" 0x43
  | bestBidAndOfferAppendage (message : BestBidAndOfferAppendage) -- "O" 0x4F
  | noBestBidChangeOrBestOfferChange (message : BboAbsent) -- "A" 0x41
  | noBestBidChangeQuoteContainsBestOffer (message : BboAbsent) -- "B" 0x42
  | noBestBidChangeNoBestOffer (message : BboAbsent) -- "D" 0x44
  | quoteContainsBestBidNoBestOfferChange (message : BboAbsent) -- "E" 0x45
  | quoteContainsBestBidQuoteContainsBestOffer (message : BboAbsent) -- "F" 0x46
  | quoteContainsBestBidBestOfferAppendage (message : BboAbsent) -- "G" 0x47
  | quoteContainsBestBidNoBestOffer (message : BboAbsent) -- "H" 0x48
  | noBestBidNoBestOfferChange (message : BboAbsent) -- "I" 0x49
  | noBestBidQuoteContainsBestOffer (message : BboAbsent) -- "J" 0x4A
  | noBestBidBestOfferAppendage (message : BboAbsent) -- "K" 0x4B
  | noBestBidNoBestOffer (message : BboAbsent) -- "L" 0x4C
  | bestBidAppendageQuoteContainsBestOffer (message : BboAbsent) -- "N" 0x4E
  | bestBidAppendageNoBestOffer (message : BboAbsent) -- "P" 0x50
  | notIncludedInTheBbo (message : BboAbsent) -- " " 0x20
  deriving DecidableEq, Repr

namespace BboChoice

/-- The Bbo Indicator each message is sent under -/
def tag : BboChoice → BitVec 8
  | .bestBidAppendage _ => 77
  | .bestOfferAppendage _ => 67
  | .bestBidAndOfferAppendage _ => 79
  | .noBestBidChangeOrBestOfferChange _ => 65
  | .noBestBidChangeQuoteContainsBestOffer _ => 66
  | .noBestBidChangeNoBestOffer _ => 68
  | .quoteContainsBestBidNoBestOfferChange _ => 69
  | .quoteContainsBestBidQuoteContainsBestOffer _ => 70
  | .quoteContainsBestBidBestOfferAppendage _ => 71
  | .quoteContainsBestBidNoBestOffer _ => 72
  | .noBestBidNoBestOfferChange _ => 73
  | .noBestBidQuoteContainsBestOffer _ => 74
  | .noBestBidBestOfferAppendage _ => 75
  | .noBestBidNoBestOffer _ => 76
  | .bestBidAppendageQuoteContainsBestOffer _ => 78
  | .bestBidAppendageNoBestOffer _ => 80
  | .notIncludedInTheBbo _ => 32

def encode : BboChoice → List UInt8
  | .bestBidAppendage message => BestBidAppendage.encode message
  | .bestOfferAppendage message => BestOfferAppendage.encode message
  | .bestBidAndOfferAppendage message => BestBidAndOfferAppendage.encode message
  | .noBestBidChangeOrBestOfferChange message => BboAbsent.encode message
  | .noBestBidChangeQuoteContainsBestOffer message => BboAbsent.encode message
  | .noBestBidChangeNoBestOffer message => BboAbsent.encode message
  | .quoteContainsBestBidNoBestOfferChange message => BboAbsent.encode message
  | .quoteContainsBestBidQuoteContainsBestOffer message => BboAbsent.encode message
  | .quoteContainsBestBidBestOfferAppendage message => BboAbsent.encode message
  | .quoteContainsBestBidNoBestOffer message => BboAbsent.encode message
  | .noBestBidNoBestOfferChange message => BboAbsent.encode message
  | .noBestBidQuoteContainsBestOffer message => BboAbsent.encode message
  | .noBestBidBestOfferAppendage message => BboAbsent.encode message
  | .noBestBidNoBestOffer message => BboAbsent.encode message
  | .bestBidAppendageQuoteContainsBestOffer message => BboAbsent.encode message
  | .bestBidAppendageNoBestOffer message => BboAbsent.encode message
  | .notIncludedInTheBbo message => BboAbsent.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : BboChoice) : (encode message).length ≤ 20 := by
  cases message with
  | bestBidAppendage inner =>
    simp only [encode, BestBidAppendage.encode_length]
    omega
  | bestOfferAppendage inner =>
    simp only [encode, BestOfferAppendage.encode_length]
    omega
  | bestBidAndOfferAppendage inner =>
    simp only [encode, BestBidAndOfferAppendage.encode_length]
    omega
  | noBestBidChangeOrBestOfferChange inner =>
    simp only [encode, BboAbsent.encode_length]
    omega
  | noBestBidChangeQuoteContainsBestOffer inner =>
    simp only [encode, BboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOffer inner =>
    simp only [encode, BboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOfferChange inner =>
    simp only [encode, BboAbsent.encode_length]
    omega
  | quoteContainsBestBidQuoteContainsBestOffer inner =>
    simp only [encode, BboAbsent.encode_length]
    omega
  | quoteContainsBestBidBestOfferAppendage inner =>
    simp only [encode, BboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOffer inner =>
    simp only [encode, BboAbsent.encode_length]
    omega
  | noBestBidNoBestOfferChange inner =>
    simp only [encode, BboAbsent.encode_length]
    omega
  | noBestBidQuoteContainsBestOffer inner =>
    simp only [encode, BboAbsent.encode_length]
    omega
  | noBestBidBestOfferAppendage inner =>
    simp only [encode, BboAbsent.encode_length]
    omega
  | noBestBidNoBestOffer inner =>
    simp only [encode, BboAbsent.encode_length]
    omega
  | bestBidAppendageQuoteContainsBestOffer inner =>
    simp only [encode, BboAbsent.encode_length]
    omega
  | bestBidAppendageNoBestOffer inner =>
    simp only [encode, BboAbsent.encode_length]
    omega
  | notIncludedInTheBbo inner =>
    simp only [encode, BboAbsent.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (BboChoice × List UInt8) :=
  if tag = 77 then (BestBidAppendage.decode bytes).map fun (message, rest) => (.bestBidAppendage message, rest)
  else if tag = 67 then (BestOfferAppendage.decode bytes).map fun (message, rest) => (.bestOfferAppendage message, rest)
  else if tag = 79 then (BestBidAndOfferAppendage.decode bytes).map fun (message, rest) => (.bestBidAndOfferAppendage message, rest)
  else if tag = 65 then (BboAbsent.decode bytes).map fun (message, rest) => (.noBestBidChangeOrBestOfferChange message, rest)
  else if tag = 66 then (BboAbsent.decode bytes).map fun (message, rest) => (.noBestBidChangeQuoteContainsBestOffer message, rest)
  else if tag = 68 then (BboAbsent.decode bytes).map fun (message, rest) => (.noBestBidChangeNoBestOffer message, rest)
  else if tag = 69 then (BboAbsent.decode bytes).map fun (message, rest) => (.quoteContainsBestBidNoBestOfferChange message, rest)
  else if tag = 70 then (BboAbsent.decode bytes).map fun (message, rest) => (.quoteContainsBestBidQuoteContainsBestOffer message, rest)
  else if tag = 71 then (BboAbsent.decode bytes).map fun (message, rest) => (.quoteContainsBestBidBestOfferAppendage message, rest)
  else if tag = 72 then (BboAbsent.decode bytes).map fun (message, rest) => (.quoteContainsBestBidNoBestOffer message, rest)
  else if tag = 73 then (BboAbsent.decode bytes).map fun (message, rest) => (.noBestBidNoBestOfferChange message, rest)
  else if tag = 74 then (BboAbsent.decode bytes).map fun (message, rest) => (.noBestBidQuoteContainsBestOffer message, rest)
  else if tag = 75 then (BboAbsent.decode bytes).map fun (message, rest) => (.noBestBidBestOfferAppendage message, rest)
  else if tag = 76 then (BboAbsent.decode bytes).map fun (message, rest) => (.noBestBidNoBestOffer message, rest)
  else if tag = 78 then (BboAbsent.decode bytes).map fun (message, rest) => (.bestBidAppendageQuoteContainsBestOffer message, rest)
  else if tag = 80 then (BboAbsent.decode bytes).map fun (message, rest) => (.bestBidAppendageNoBestOffer message, rest)
  else if tag = 32 then (BboAbsent.decode bytes).map fun (message, rest) => (.notIncludedInTheBbo message, rest)
  else none

@[simp] theorem decode_encode (message : BboChoice) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end BboChoice

/-- Long Equity And Index Quote Message -/
structure LongEquityAndIndexQuoteMessage where
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 32
  securitySymbol : Alpha 5
  reserved1 : Alpha 1
  expirationBlock : ExpirationBlock
  strikePriceDenominatorCode : StrikePriceDenominatorCode
  strikePrice : BitVec 32
  premiumPriceDenominatorCode : PremiumPriceDenominatorCode
  bidPrice : BitVec 32
  bidSize : BitVec 32
  offerPrice : BitVec 32
  offerSize : BitVec 32
  bboChoice : BboChoice
  deriving DecidableEq, Repr

namespace LongEquityAndIndexQuoteMessage

def encode (message : LongEquityAndIndexQuoteMessage) : List UInt8 :=
  encodeUInt 1 (BboChoice.tag message.bboChoice)
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.reserved1
    ++ (ExpirationBlock.encode message.expirationBlock
    ++ (StrikePriceDenominatorCode.encode message.strikePriceDenominatorCode
    ++ (encodeUInt 4 message.strikePrice
    ++ (PremiumPriceDenominatorCode.encode message.premiumPriceDenominatorCode
    ++ (encodeUInt 4 message.bidPrice
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 4 message.offerPrice
    ++ (encodeUInt 4 message.offerSize
    ++ (BboChoice.encode message.bboChoice)))))))))))))

def decode (bytes : List UInt8) : Option (LongEquityAndIndexQuoteMessage × List UInt8) := do
  let (bboIndicator, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (expirationBlock, bytes) ← ExpirationBlock.decode bytes
  let (strikePriceDenominatorCode, bytes) ← StrikePriceDenominatorCode.decode bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (premiumPriceDenominatorCode, bytes) ← PremiumPriceDenominatorCode.decode bytes
  let (bidPrice, bytes) ← decodeUInt 4 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (offerPrice, bytes) ← decodeUInt 4 bytes
  let (offerSize, bytes) ← decodeUInt 4 bytes
  let (bboChoice, bytes) ← BboChoice.decode bboIndicator bytes
  pure ({ transactionId, participantReferenceNumber, securitySymbol, reserved1, expirationBlock, strikePriceDenominatorCode, strikePrice, premiumPriceDenominatorCode, bidPrice, bidSize, offerPrice, offerSize, bboChoice }, bytes)

theorem encode_length_pos (message : LongEquityAndIndexQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongEquityAndIndexQuoteMessage) : (encode message).length ≤ 60 := by
  unfold encode
  cases message.bboChoice with
  | bestBidAppendage inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BestBidAppendage.encode_length]
    omega
  | bestOfferAppendage inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BestOfferAppendage.encode_length]
    omega
  | bestBidAndOfferAppendage inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BestBidAndOfferAppendage.encode_length]
    omega
  | noBestBidChangeOrBestOfferChange inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega
  | noBestBidChangeQuoteContainsBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOfferChange inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega
  | quoteContainsBestBidQuoteContainsBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega
  | quoteContainsBestBidBestOfferAppendage inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega
  | noBestBidNoBestOfferChange inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega
  | noBestBidQuoteContainsBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega
  | noBestBidBestOfferAppendage inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega
  | noBestBidNoBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega
  | bestBidAppendageQuoteContainsBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega
  | bestBidAppendageNoBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega
  | notIncludedInTheBbo inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, StrikePriceDenominatorCode.encode_length, PremiumPriceDenominatorCode.encode_length, BboAbsent.encode_length]
    omega

@[simp] theorem decode_encode (message : LongEquityAndIndexQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ExpirationBlock.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PremiumPriceDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [BboChoice.decode_encode, some_bind]
  rfl

end LongEquityAndIndexQuoteMessage

/-- Any Long Equity And Index Quote Message Payload, selected by Long Equity And Index Quote Message Type -/
inductive LongEquityAndIndexQuoteMessagePayload where
  | longEquityAndIndexQuoteMessage (message : LongEquityAndIndexQuoteMessage) -- " " 0x20
  deriving DecidableEq, Repr

namespace LongEquityAndIndexQuoteMessagePayload

/-- The Long Equity And Index Quote Message Type each message is sent under -/
def tag : LongEquityAndIndexQuoteMessagePayload → BitVec 8
  | .longEquityAndIndexQuoteMessage _ => 32

def encode : LongEquityAndIndexQuoteMessagePayload → List UInt8
  | .longEquityAndIndexQuoteMessage message => LongEquityAndIndexQuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : LongEquityAndIndexQuoteMessagePayload) : (encode message).length ≤ 60 := by
  cases message with
  | longEquityAndIndexQuoteMessage inner =>
    have bound_inner := LongEquityAndIndexQuoteMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (LongEquityAndIndexQuoteMessagePayload × List UInt8) :=
  if tag = 32 then (LongEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : LongEquityAndIndexQuoteMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end LongEquityAndIndexQuoteMessagePayload

/-- Long Equity And Index Quote Category -/
structure LongEquityAndIndexQuoteCategory where
  longEquityAndIndexQuoteMessagePayload : LongEquityAndIndexQuoteMessagePayload
  deriving DecidableEq, Repr

namespace LongEquityAndIndexQuoteCategory

def encode (message : LongEquityAndIndexQuoteCategory) : List UInt8 :=
  encodeUInt 1 (LongEquityAndIndexQuoteMessagePayload.tag message.longEquityAndIndexQuoteMessagePayload)
    ++ (LongEquityAndIndexQuoteMessagePayload.encode message.longEquityAndIndexQuoteMessagePayload)

def decode (bytes : List UInt8) : Option (LongEquityAndIndexQuoteCategory × List UInt8) := do
  let (longEquityAndIndexQuoteMessageType, bytes) ← decodeUInt 1 bytes
  let (longEquityAndIndexQuoteMessagePayload, bytes) ← LongEquityAndIndexQuoteMessagePayload.decode longEquityAndIndexQuoteMessageType bytes
  pure ({ longEquityAndIndexQuoteMessagePayload }, bytes)

theorem encode_length_pos (message : LongEquityAndIndexQuoteCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongEquityAndIndexQuoteCategory) : (encode message).length ≤ 61 := by
  unfold encode
  cases message.longEquityAndIndexQuoteMessagePayload with
  | longEquityAndIndexQuoteMessage inner =>
    have bound_inner := LongEquityAndIndexQuoteMessage.encode_length_le inner
    simp only [LongEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : LongEquityAndIndexQuoteCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [LongEquityAndIndexQuoteMessagePayload.decode_encode, some_bind]
  rfl

end LongEquityAndIndexQuoteCategory

/-- Short Equity And Index Quote Message -/
structure ShortEquityAndIndexQuoteMessage where
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 32
  securitySymbolShort : Alpha 4
  expirationBlock : ExpirationBlock
  strikePriceShort : BitVec 16
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  offerPriceShort : BitVec 16
  offerSizeShort : BitVec 16
  bboChoice : BboChoice
  deriving DecidableEq, Repr

namespace ShortEquityAndIndexQuoteMessage

def encode (message : ShortEquityAndIndexQuoteMessage) : List UInt8 :=
  encodeUInt 1 (BboChoice.tag message.bboChoice)
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbolShort
    ++ (ExpirationBlock.encode message.expirationBlock
    ++ (encodeUInt 2 message.strikePriceShort
    ++ (encodeUInt 2 message.bidPriceShort
    ++ (encodeUInt 2 message.bidSizeShort
    ++ (encodeUInt 2 message.offerPriceShort
    ++ (encodeUInt 2 message.offerSizeShort
    ++ (BboChoice.encode message.bboChoice))))))))))

def decode (bytes : List UInt8) : Option (ShortEquityAndIndexQuoteMessage × List UInt8) := do
  let (bboIndicator, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (securitySymbolShort, bytes) ← Alpha.decode 4 bytes
  let (expirationBlock, bytes) ← ExpirationBlock.decode bytes
  let (strikePriceShort, bytes) ← decodeUInt 2 bytes
  let (bidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bidSizeShort, bytes) ← decodeUInt 2 bytes
  let (offerPriceShort, bytes) ← decodeUInt 2 bytes
  let (offerSizeShort, bytes) ← decodeUInt 2 bytes
  let (bboChoice, bytes) ← BboChoice.decode bboIndicator bytes
  pure ({ transactionId, participantReferenceNumber, securitySymbolShort, expirationBlock, strikePriceShort, bidPriceShort, bidSizeShort, offerPriceShort, offerSizeShort, bboChoice }, bytes)

theorem encode_length_pos (message : ShortEquityAndIndexQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ShortEquityAndIndexQuoteMessage) : (encode message).length ≤ 46 := by
  unfold encode
  cases message.bboChoice with
  | bestBidAppendage inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BestBidAppendage.encode_length]
    omega
  | bestOfferAppendage inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BestOfferAppendage.encode_length]
    omega
  | bestBidAndOfferAppendage inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BestBidAndOfferAppendage.encode_length]
    omega
  | noBestBidChangeOrBestOfferChange inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega
  | noBestBidChangeQuoteContainsBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega
  | noBestBidChangeNoBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOfferChange inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega
  | quoteContainsBestBidQuoteContainsBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega
  | quoteContainsBestBidBestOfferAppendage inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega
  | quoteContainsBestBidNoBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega
  | noBestBidNoBestOfferChange inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega
  | noBestBidQuoteContainsBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega
  | noBestBidBestOfferAppendage inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega
  | noBestBidNoBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega
  | bestBidAppendageQuoteContainsBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega
  | bestBidAppendageNoBestOffer inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega
  | notIncludedInTheBbo inner =>
    simp only [BboChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ExpirationBlock.encode_length, BboAbsent.encode_length]
    omega

@[simp] theorem decode_encode (message : ShortEquityAndIndexQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpirationBlock.decode_encode, some_bind]
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
  rw [BboChoice.decode_encode, some_bind]
  rfl

end ShortEquityAndIndexQuoteMessage

/-- Any Short Equity And Index Quote Message Payload, selected by Short Equity And Index Quote Message Type -/
inductive ShortEquityAndIndexQuoteMessagePayload where
  | shortEquityAndIndexQuoteMessage (message : ShortEquityAndIndexQuoteMessage) -- " " 0x20
  deriving DecidableEq, Repr

namespace ShortEquityAndIndexQuoteMessagePayload

/-- The Short Equity And Index Quote Message Type each message is sent under -/
def tag : ShortEquityAndIndexQuoteMessagePayload → BitVec 8
  | .shortEquityAndIndexQuoteMessage _ => 32

def encode : ShortEquityAndIndexQuoteMessagePayload → List UInt8
  | .shortEquityAndIndexQuoteMessage message => ShortEquityAndIndexQuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ShortEquityAndIndexQuoteMessagePayload) : (encode message).length ≤ 46 := by
  cases message with
  | shortEquityAndIndexQuoteMessage inner =>
    have bound_inner := ShortEquityAndIndexQuoteMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ShortEquityAndIndexQuoteMessagePayload × List UInt8) :=
  if tag = 32 then (ShortEquityAndIndexQuoteMessage.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ShortEquityAndIndexQuoteMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ShortEquityAndIndexQuoteMessagePayload

/-- Short Equity And Index Quote Category -/
structure ShortEquityAndIndexQuoteCategory where
  shortEquityAndIndexQuoteMessagePayload : ShortEquityAndIndexQuoteMessagePayload
  deriving DecidableEq, Repr

namespace ShortEquityAndIndexQuoteCategory

def encode (message : ShortEquityAndIndexQuoteCategory) : List UInt8 :=
  encodeUInt 1 (ShortEquityAndIndexQuoteMessagePayload.tag message.shortEquityAndIndexQuoteMessagePayload)
    ++ (ShortEquityAndIndexQuoteMessagePayload.encode message.shortEquityAndIndexQuoteMessagePayload)

def decode (bytes : List UInt8) : Option (ShortEquityAndIndexQuoteCategory × List UInt8) := do
  let (shortEquityAndIndexQuoteMessageType, bytes) ← decodeUInt 1 bytes
  let (shortEquityAndIndexQuoteMessagePayload, bytes) ← ShortEquityAndIndexQuoteMessagePayload.decode shortEquityAndIndexQuoteMessageType bytes
  pure ({ shortEquityAndIndexQuoteMessagePayload }, bytes)

theorem encode_length_pos (message : ShortEquityAndIndexQuoteCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ShortEquityAndIndexQuoteCategory) : (encode message).length ≤ 47 := by
  unfold encode
  cases message.shortEquityAndIndexQuoteMessagePayload with
  | shortEquityAndIndexQuoteMessage inner =>
    have bound_inner := ShortEquityAndIndexQuoteMessage.encode_length_le inner
    simp only [ShortEquityAndIndexQuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : ShortEquityAndIndexQuoteCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ShortEquityAndIndexQuoteMessagePayload.decode_encode, some_bind]
  rfl

end ShortEquityAndIndexQuoteCategory

/-- Underlying Value Last Sale Message: 24 bytes -/
structure UnderlyingValueLastSaleMessage where
  messageIndicator : Alpha 1
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 32
  securitySymbol : Alpha 5
  reserved1 : Alpha 1
  indexValueDenominatorCode : IndexValueDenominatorCode
  indexValue : BitVec 32
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace UnderlyingValueLastSaleMessage

def encode (message : UnderlyingValueLastSaleMessage) : List UInt8 :=
  Alpha.encode message.messageIndicator
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.reserved1
    ++ (IndexValueDenominatorCode.encode message.indexValueDenominatorCode
    ++ (encodeUInt 4 message.indexValue
    ++ (Alpha.encode message.reserved4)))))))

def decode (bytes : List UInt8) : Option (UnderlyingValueLastSaleMessage × List UInt8) := do
  let (messageIndicator, bytes) ← Alpha.decode 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (indexValueDenominatorCode, bytes) ← IndexValueDenominatorCode.decode bytes
  let (indexValue, bytes) ← decodeUInt 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ messageIndicator, transactionId, participantReferenceNumber, securitySymbol, reserved1, indexValueDenominatorCode, indexValue, reserved4 }, bytes)

@[simp] theorem encode_length (message : UnderlyingValueLastSaleMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, IndexValueDenominatorCode.encode_length]

theorem encode_length_pos (message : UnderlyingValueLastSaleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingValueLastSaleMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IndexValueDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingValueLastSaleMessage

/-- Underlying Value Bid And Offer Message: 28 bytes -/
structure UnderlyingValueBidAndOfferMessage where
  messageIndicator : Alpha 1
  transactionId : BitVec 32
  participantReferenceNumber : BitVec 32
  securitySymbol : Alpha 5
  reserved1 : Alpha 1
  indexValueDenominatorCode : IndexValueDenominatorCode
  bidIndexValue : BitVec 32
  offerIndexValue : BitVec 64
  deriving DecidableEq, Repr

namespace UnderlyingValueBidAndOfferMessage

def encode (message : UnderlyingValueBidAndOfferMessage) : List UInt8 :=
  Alpha.encode message.messageIndicator
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 4 message.participantReferenceNumber
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.reserved1
    ++ (IndexValueDenominatorCode.encode message.indexValueDenominatorCode
    ++ (encodeUInt 4 message.bidIndexValue
    ++ (encodeUInt 8 message.offerIndexValue)))))))

def decode (bytes : List UInt8) : Option (UnderlyingValueBidAndOfferMessage × List UInt8) := do
  let (messageIndicator, bytes) ← Alpha.decode 1 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (indexValueDenominatorCode, bytes) ← IndexValueDenominatorCode.decode bytes
  let (bidIndexValue, bytes) ← decodeUInt 4 bytes
  let (offerIndexValue, bytes) ← decodeUInt 8 bytes
  pure ({ messageIndicator, transactionId, participantReferenceNumber, securitySymbol, reserved1, indexValueDenominatorCode, bidIndexValue, offerIndexValue }, bytes)

@[simp] theorem encode_length (message : UnderlyingValueBidAndOfferMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, IndexValueDenominatorCode.encode_length]

theorem encode_length_pos (message : UnderlyingValueBidAndOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingValueBidAndOfferMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IndexValueDenominatorCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end UnderlyingValueBidAndOfferMessage

/-- Any Underlying Value Message Payload, selected by Underlying Value Message Type -/
inductive UnderlyingValueMessagePayload where
  | underlyingValueLastSaleMessage (message : UnderlyingValueLastSaleMessage) -- " " 0x20
  | underlyingValueBidAndOfferMessage (message : UnderlyingValueBidAndOfferMessage) -- "I" 0x49
  deriving DecidableEq, Repr

namespace UnderlyingValueMessagePayload

/-- The Underlying Value Message Type each message is sent under -/
def tag : UnderlyingValueMessagePayload → BitVec 8
  | .underlyingValueLastSaleMessage _ => 32
  | .underlyingValueBidAndOfferMessage _ => 73

def encode : UnderlyingValueMessagePayload → List UInt8
  | .underlyingValueLastSaleMessage message => UnderlyingValueLastSaleMessage.encode message
  | .underlyingValueBidAndOfferMessage message => UnderlyingValueBidAndOfferMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnderlyingValueMessagePayload) : (encode message).length ≤ 28 := by
  cases message with
  | underlyingValueLastSaleMessage inner =>
    simp only [encode, UnderlyingValueLastSaleMessage.encode_length]
    omega
  | underlyingValueBidAndOfferMessage inner =>
    simp only [encode, UnderlyingValueBidAndOfferMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnderlyingValueMessagePayload × List UInt8) :=
  if tag = 32 then (UnderlyingValueLastSaleMessage.decode bytes).map fun (message, rest) => (.underlyingValueLastSaleMessage message, rest)
  else if tag = 73 then (UnderlyingValueBidAndOfferMessage.decode bytes).map fun (message, rest) => (.underlyingValueBidAndOfferMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UnderlyingValueMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnderlyingValueMessagePayload

/-- Underlying Value Category -/
structure UnderlyingValueCategory where
  underlyingValueMessagePayload : UnderlyingValueMessagePayload
  deriving DecidableEq, Repr

namespace UnderlyingValueCategory

def encode (message : UnderlyingValueCategory) : List UInt8 :=
  encodeUInt 1 (UnderlyingValueMessagePayload.tag message.underlyingValueMessagePayload)
    ++ (UnderlyingValueMessagePayload.encode message.underlyingValueMessagePayload)

def decode (bytes : List UInt8) : Option (UnderlyingValueCategory × List UInt8) := do
  let (underlyingValueMessageType, bytes) ← decodeUInt 1 bytes
  let (underlyingValueMessagePayload, bytes) ← UnderlyingValueMessagePayload.decode underlyingValueMessageType bytes
  pure ({ underlyingValueMessagePayload }, bytes)

theorem encode_length_pos (message : UnderlyingValueCategory) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnderlyingValueCategory) : (encode message).length ≤ 29 := by
  unfold encode
  cases message.underlyingValueMessagePayload with
  | underlyingValueLastSaleMessage inner =>
    simp only [UnderlyingValueMessagePayload.encode, List.length_append, encodeUInt_length, UnderlyingValueLastSaleMessage.encode_length]
    omega
  | underlyingValueBidAndOfferMessage inner =>
    simp only [UnderlyingValueMessagePayload.encode, List.length_append, encodeUInt_length, UnderlyingValueBidAndOfferMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : UnderlyingValueCategory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnderlyingValueMessagePayload.decode_encode, some_bind]
  rfl

end UnderlyingValueCategory

/-- Any Payload, selected by Message Category -/
inductive Payload where
  | administrativeCategory (message : AdministrativeCategory) -- "C" 0x43
  | controlCategory (message : ControlCategory) -- "H" 0x48
  | equityAndIndexLastSaleCategory (message : EquityAndIndexLastSaleCategory) -- "a" 0x61
  | openInterestCategory (message : OpenInterestCategory) -- "d" 0x64
  | equityAndIndexEndOfDaySummaryCategory (message : EquityAndIndexEndOfDaySummaryCategory) -- "f" 0x66
  | longEquityAndIndexQuoteCategory (message : LongEquityAndIndexQuoteCategory) -- "k" 0x6B
  | shortEquityAndIndexQuoteCategory (message : ShortEquityAndIndexQuoteCategory) -- "q" 0x71
  | underlyingValueCategory (message : UnderlyingValueCategory) -- "Y" 0x59
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Category each message is sent under -/
def tag : Payload → BitVec 8
  | .administrativeCategory _ => 67
  | .controlCategory _ => 72
  | .equityAndIndexLastSaleCategory _ => 97
  | .openInterestCategory _ => 100
  | .equityAndIndexEndOfDaySummaryCategory _ => 102
  | .longEquityAndIndexQuoteCategory _ => 107
  | .shortEquityAndIndexQuoteCategory _ => 113
  | .underlyingValueCategory _ => 89

def encode : Payload → List UInt8
  | .administrativeCategory message => AdministrativeCategory.encode message
  | .controlCategory message => ControlCategory.encode message
  | .equityAndIndexLastSaleCategory message => EquityAndIndexLastSaleCategory.encode message
  | .openInterestCategory message => OpenInterestCategory.encode message
  | .equityAndIndexEndOfDaySummaryCategory message => EquityAndIndexEndOfDaySummaryCategory.encode message
  | .longEquityAndIndexQuoteCategory message => LongEquityAndIndexQuoteCategory.encode message
  | .shortEquityAndIndexQuoteCategory message => ShortEquityAndIndexQuoteCategory.encode message
  | .underlyingValueCategory message => UnderlyingValueCategory.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 65547 := by
  cases message with
  | administrativeCategory inner =>
    have bound_inner := AdministrativeCategory.encode_length_le inner
    simp only [encode]
    omega
  | controlCategory inner =>
    have bound_inner := ControlCategory.encode_length_le inner
    simp only [encode]
    omega
  | equityAndIndexLastSaleCategory inner =>
    have bound_inner := EquityAndIndexLastSaleCategory.encode_length_le inner
    simp only [encode]
    omega
  | openInterestCategory inner =>
    have bound_inner := OpenInterestCategory.encode_length_le inner
    simp only [encode]
    omega
  | equityAndIndexEndOfDaySummaryCategory inner =>
    have bound_inner := EquityAndIndexEndOfDaySummaryCategory.encode_length_le inner
    simp only [encode]
    omega
  | longEquityAndIndexQuoteCategory inner =>
    have bound_inner := LongEquityAndIndexQuoteCategory.encode_length_le inner
    simp only [encode]
    omega
  | shortEquityAndIndexQuoteCategory inner =>
    have bound_inner := ShortEquityAndIndexQuoteCategory.encode_length_le inner
    simp only [encode]
    omega
  | underlyingValueCategory inner =>
    have bound_inner := UnderlyingValueCategory.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 67 then (AdministrativeCategory.decode bytes).map fun (message, rest) => (.administrativeCategory message, rest)
  else if tag = 72 then (ControlCategory.decode bytes).map fun (message, rest) => (.controlCategory message, rest)
  else if tag = 97 then (EquityAndIndexLastSaleCategory.decode bytes).map fun (message, rest) => (.equityAndIndexLastSaleCategory message, rest)
  else if tag = 100 then (OpenInterestCategory.decode bytes).map fun (message, rest) => (.openInterestCategory message, rest)
  else if tag = 102 then (EquityAndIndexEndOfDaySummaryCategory.decode bytes).map fun (message, rest) => (.equityAndIndexEndOfDaySummaryCategory message, rest)
  else if tag = 107 then (LongEquityAndIndexQuoteCategory.decode bytes).map fun (message, rest) => (.longEquityAndIndexQuoteCategory message, rest)
  else if tag = 113 then (ShortEquityAndIndexQuoteCategory.decode bytes).map fun (message, rest) => (.shortEquityAndIndexQuoteCategory message, rest)
  else if tag = 89 then (UnderlyingValueCategory.decode bytes).map fun (message, rest) => (.underlyingValueCategory message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  participantId : ParticipantId
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  ParticipantId.encode message.participantId
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (participantId, bytes) ← ParticipantId.decode bytes
  let (messageCategory, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageCategory bytes
  pure ({ participantId, payload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [ParticipantId.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 65549 := by
  unfold encode
  cases message.payload with
  | administrativeCategory inner =>
    have bound_inner := AdministrativeCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | controlCategory inner =>
    have bound_inner := ControlCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | equityAndIndexLastSaleCategory inner =>
    have bound_inner := EquityAndIndexLastSaleCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | openInterestCategory inner =>
    have bound_inner := OpenInterestCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | equityAndIndexEndOfDaySummaryCategory inner =>
    have bound_inner := EquityAndIndexEndOfDaySummaryCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | longEquityAndIndexQuoteCategory inner =>
    have bound_inner := LongEquityAndIndexQuoteCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | shortEquityAndIndexQuoteCategory inner =>
    have bound_inner := ShortEquityAndIndexQuoteCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega
  | underlyingValueCategory inner =>
    have bound_inner := UnderlyingValueCategory.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, ParticipantId.encode_length, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  version : BitVec 8
  blockSize : BitVec 16
  dataFeedIndicator : DataFeedIndicator
  retransmissionIndicator : RetransmissionIndicator
  sessionIndicator : BitVec 8
  blockSequenceNumber : BitVec 32
  blockTimestamp : BlockTimestamp
  blockChecksum : BitVec 16
  message : Bounded 1 Message
  blockPadByte : Capped 1
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.version
    ++ (encodeUInt 2 message.blockSize
    ++ (DataFeedIndicator.encode message.dataFeedIndicator
    ++ (RetransmissionIndicator.encode message.retransmissionIndicator
    ++ (encodeUInt 1 message.sessionIndicator
    ++ (encodeUInt 4 message.blockSequenceNumber
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (BlockTimestamp.encode message.blockTimestamp
    ++ (encodeUInt 2 message.blockChecksum
    ++ (encodeMany Message.encode message.message.val
    ++ (message.blockPadByte.val))))))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (version, bytes) ← decodeUInt 1 bytes
  let (blockSize, bytes) ← decodeUInt 2 bytes
  let (dataFeedIndicator, bytes) ← DataFeedIndicator.decode bytes
  let (retransmissionIndicator, bytes) ← RetransmissionIndicator.decode bytes
  let (sessionIndicator, bytes) ← decodeUInt 1 bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (messagesInBlock, bytes) ← decodeUInt 1 bytes
  let (blockTimestamp, bytes) ← BlockTimestamp.decode bytes
  let (blockChecksum, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messagesInBlock.toNat bytes
  let blockPadByte_ := bytes
  if fits_message : message_.length < 256 ^ 1 then
    if fits_blockPadByte : blockPadByte_.length ≤ 1 then
      pure { version, blockSize, dataFeedIndicator, retransmissionIndicator, sessionIndicator, blockSequenceNumber, blockTimestamp, blockChecksum, message := ⟨message_, fits_message⟩, blockPadByte := ⟨blockPadByte_, fits_blockPadByte⟩ }
    else none
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 16715017 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 65549 Message.encode_length_le message.message.val
  have bound_blockPadByte := message.blockPadByte.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, DataFeedIndicator.encode_length, RetransmissionIndicator.encode_length, BlockTimestamp.encode_length]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [DataFeedIndicator.decode_encode, some_bind]
  dsimp only
  rw [RetransmissionIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [BlockTimestamp.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt, dite_eq_left message.blockPadByte.length_le]
  rfl

end Packet

end Omi.SiacOpraOutputObiV62
