import Omi.Wire

/-!
# CME Group Market Data Platform 3 v1.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Match Event Indicator is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Settl Price Type is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Inst Attrib Value is a bit field set, proven as its 4 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CmeGlobexMdp3SbeV15Udp

/-- Security Update Action: one byte code -/
def SecurityUpdateAction.codes : List UInt8 :=
  [0x41, 0x44, 0x4D]

inductive SecurityUpdateAction where
  | add -- Add
  | delete -- Delete
  | modify -- Modify
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityUpdateAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityUpdateAction

def toByte : SecurityUpdateAction → UInt8
  | .add => 0x41
  | .delete => 0x44
  | .modify => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityUpdateAction :=
  if byte = 0x41 then .add
  else if byte = 0x44 then .delete
  else .modify

def ofByte (byte : UInt8) : SecurityUpdateAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityUpdateAction) : ofByte value.toByte = value := by
  cases value with
  | add => decide
  | delete => decide
  | modify => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityUpdateAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityUpdateAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityUpdateAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityUpdateAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityUpdateAction

/-- Md Entry Type Book: one byte code -/
def MdEntryTypeBook.codes : List UInt8 :=
  [0x30, 0x31, 0x45, 0x46, 0x4A]

inductive MdEntryTypeBook where
  | bid -- Bid
  | offer -- Offer
  | impliedBid -- Implied Bid
  | impliedOffer -- Implied Offer
  | bookReset -- Book Reset
  | unlisted (byte : { byte : UInt8 // byte ∉ MdEntryTypeBook.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MdEntryTypeBook

def toByte : MdEntryTypeBook → UInt8
  | .bid => 0x30
  | .offer => 0x31
  | .impliedBid => 0x45
  | .impliedOffer => 0x46
  | .bookReset => 0x4A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MdEntryTypeBook :=
  if byte = 0x30 then .bid
  else if byte = 0x31 then .offer
  else if byte = 0x45 then .impliedBid
  else if byte = 0x46 then .impliedOffer
  else .bookReset

def ofByte (byte : UInt8) : MdEntryTypeBook :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MdEntryTypeBook) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | offer => decide
  | impliedBid => decide
  | impliedOffer => decide
  | bookReset => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MdEntryTypeBook) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeBook × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeBook) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeBook) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MdEntryTypeBook

/-- Md Entry Type Daily Statistics: one byte code -/
def MdEntryTypeDailyStatistics.codes : List UInt8 :=
  [0x36, 0x42, 0x43, 0x57]

inductive MdEntryTypeDailyStatistics where
  | settlementPrice -- Settlement Price
  | clearedVolume -- Cleared Volume
  | openInterest -- Open Interest
  | fixingPrice -- Fixing Price
  | unlisted (byte : { byte : UInt8 // byte ∉ MdEntryTypeDailyStatistics.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MdEntryTypeDailyStatistics

def toByte : MdEntryTypeDailyStatistics → UInt8
  | .settlementPrice => 0x36
  | .clearedVolume => 0x42
  | .openInterest => 0x43
  | .fixingPrice => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MdEntryTypeDailyStatistics :=
  if byte = 0x36 then .settlementPrice
  else if byte = 0x42 then .clearedVolume
  else if byte = 0x43 then .openInterest
  else .fixingPrice

def ofByte (byte : UInt8) : MdEntryTypeDailyStatistics :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MdEntryTypeDailyStatistics) : ofByte value.toByte = value := by
  cases value with
  | settlementPrice => decide
  | clearedVolume => decide
  | openInterest => decide
  | fixingPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MdEntryTypeDailyStatistics) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeDailyStatistics × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeDailyStatistics) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeDailyStatistics) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MdEntryTypeDailyStatistics

/-- Md Entry Type Statistics: one byte code -/
def MdEntryTypeStatistics.codes : List UInt8 :=
  [0x34, 0x37, 0x38, 0x4E, 0x4F]

inductive MdEntryTypeStatistics where
  | openPrice -- Open Price
  | highTrade -- High Trade
  | lowTrade -- Low Trade
  | highestBid -- Highest Bid
  | lowestOffer -- Lowest Offer
  | unlisted (byte : { byte : UInt8 // byte ∉ MdEntryTypeStatistics.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MdEntryTypeStatistics

def toByte : MdEntryTypeStatistics → UInt8
  | .openPrice => 0x34
  | .highTrade => 0x37
  | .lowTrade => 0x38
  | .highestBid => 0x4E
  | .lowestOffer => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MdEntryTypeStatistics :=
  if byte = 0x34 then .openPrice
  else if byte = 0x37 then .highTrade
  else if byte = 0x38 then .lowTrade
  else if byte = 0x4E then .highestBid
  else .lowestOffer

def ofByte (byte : UInt8) : MdEntryTypeStatistics :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MdEntryTypeStatistics) : ofByte value.toByte = value := by
  cases value with
  | openPrice => decide
  | highTrade => decide
  | lowTrade => decide
  | highestBid => decide
  | lowestOffer => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MdEntryTypeStatistics) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeStatistics × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeStatistics) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeStatistics) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MdEntryTypeStatistics

/-- Md Entry Type: one byte code -/
def MdEntryType.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x34, 0x36, 0x37, 0x38, 0x42, 0x43, 0x45, 0x46, 0x4A, 0x4E, 0x4F, 0x57, 0x65, 0x67]

inductive MdEntryType where
  | bid -- Bid
  | offer -- Offer
  | trade -- Trade
  | openingPrice -- Opening Price
  | settlementPrice -- Settlement Price
  | tradingSessionHighPrice -- Trading Session High Price
  | tradingSessionLowPrice -- Trading Session Low Price
  | tradeVolume -- Trade Volume
  | openInterest -- Open Interest
  | impliedBid -- Implied Bid
  | impliedOffer -- Implied Offer
  | emptyBook -- Empty Book
  | sessionHighBid -- Session High Bid
  | sessionLowOffer -- Session Low Offer
  | fixingPrice -- Fixing Price
  | electronicVolume -- Electronic Volume
  | thresholdLimitsandPriceBandVariation -- Threshold Limitsand Price Band Variation
  | unlisted (byte : { byte : UInt8 // byte ∉ MdEntryType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MdEntryType

def toByte : MdEntryType → UInt8
  | .bid => 0x30
  | .offer => 0x31
  | .trade => 0x32
  | .openingPrice => 0x34
  | .settlementPrice => 0x36
  | .tradingSessionHighPrice => 0x37
  | .tradingSessionLowPrice => 0x38
  | .tradeVolume => 0x42
  | .openInterest => 0x43
  | .impliedBid => 0x45
  | .impliedOffer => 0x46
  | .emptyBook => 0x4A
  | .sessionHighBid => 0x4E
  | .sessionLowOffer => 0x4F
  | .fixingPrice => 0x57
  | .electronicVolume => 0x65
  | .thresholdLimitsandPriceBandVariation => 0x67
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MdEntryType :=
  if byte = 0x30 then .bid
  else if byte = 0x31 then .offer
  else if byte = 0x32 then .trade
  else if byte = 0x34 then .openingPrice
  else if byte = 0x36 then .settlementPrice
  else if byte = 0x37 then .tradingSessionHighPrice
  else if byte = 0x38 then .tradingSessionLowPrice
  else if byte = 0x42 then .tradeVolume
  else if byte = 0x43 then .openInterest
  else if byte = 0x45 then .impliedBid
  else if byte = 0x46 then .impliedOffer
  else if byte = 0x4A then .emptyBook
  else if byte = 0x4E then .sessionHighBid
  else if byte = 0x4F then .sessionLowOffer
  else if byte = 0x57 then .fixingPrice
  else if byte = 0x65 then .electronicVolume
  else .thresholdLimitsandPriceBandVariation

def ofByte (byte : UInt8) : MdEntryType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MdEntryType) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | offer => decide
  | trade => decide
  | openingPrice => decide
  | settlementPrice => decide
  | tradingSessionHighPrice => decide
  | tradingSessionLowPrice => decide
  | tradeVolume => decide
  | openInterest => decide
  | impliedBid => decide
  | impliedOffer => decide
  | emptyBook => decide
  | sessionHighBid => decide
  | sessionLowOffer => decide
  | fixingPrice => decide
  | electronicVolume => decide
  | thresholdLimitsandPriceBandVariation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MdEntryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MdEntryType

/-- Binary Packet Header: 12 bytes -/
structure BinaryPacketHeader where
  packetSequenceNumber : BitVec 32
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace BinaryPacketHeader

def encode (message : BinaryPacketHeader) : List UInt8 :=
  encodeUIntLE 4 message.packetSequenceNumber
    ++ (encodeUIntLE 8 message.sendingTime)

def decode (bytes : List UInt8) : Option (BinaryPacketHeader × List UInt8) := do
  let (packetSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ packetSequenceNumber, sendingTime }, bytes)

@[simp] theorem encode_length (message : BinaryPacketHeader) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BinaryPacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BinaryPacketHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BinaryPacketHeader

/-- Channel Reset Group: 2 bytes -/
structure ChannelResetGroup where
  applId : BitVec 16
  deriving DecidableEq, Repr

namespace ChannelResetGroup

def encode (message : ChannelResetGroup) : List UInt8 :=
  encodeUIntLE 2 message.applId

def decode (bytes : List UInt8) : Option (ChannelResetGroup × List UInt8) := do
  let (applId, bytes) ← decodeUIntLE 2 bytes
  pure ({ applId }, bytes)

@[simp] theorem encode_length (message : ChannelResetGroup) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : ChannelResetGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ChannelResetGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ChannelResetGroup

/-- Channel Reset Groups -/
structure ChannelResetGroups where
  blockLength : BitVec 16
  channelResetGroup : Bounded 1 ChannelResetGroup
  deriving DecidableEq, Repr

namespace ChannelResetGroups

def encode (message : ChannelResetGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.channelResetGroup.val.length)
    ++ (encodeMany ChannelResetGroup.encode message.channelResetGroup.val))

def decode (bytes : List UInt8) : Option (ChannelResetGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (channelResetGroup_, bytes) ← decodeMany ChannelResetGroup.decode numInGroup.toNat bytes
  if fits_channelResetGroup : channelResetGroup_.length < 256 ^ 1 then
    pure ({ blockLength, channelResetGroup := ⟨channelResetGroup_, fits_channelResetGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ChannelResetGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ChannelResetGroups) : (encode message).length ≤ 513 := by
  have bound_channelResetGroup := message.channelResetGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const ChannelResetGroup.encode 2 ChannelResetGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : ChannelResetGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 ChannelResetGroup.encode ChannelResetGroup.decode ChannelResetGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.channelResetGroup.length_lt]
  rfl

end ChannelResetGroups

/-- Channel Reset -/
structure ChannelReset where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  channelResetGroups : ChannelResetGroups
  deriving DecidableEq, Repr

namespace ChannelReset

def encode (message : ChannelReset) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (ChannelResetGroups.encode message.channelResetGroups))

def decode (bytes : List UInt8) : Option (ChannelReset × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (channelResetGroups, bytes) ← ChannelResetGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, channelResetGroups }, bytes)

theorem encode_length_pos (message : ChannelReset) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ChannelReset) : (encode message).length ≤ 522 := by
  have bound_channelResetGroups := ChannelResetGroups.encode_length_le message.channelResetGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : ChannelReset) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ChannelResetGroups.decode_encode, some_bind]
  rfl

end ChannelReset

/-- Admin Heartbeat: 0 bytes -/
structure AdminHeartbeat where
  deriving DecidableEq, Repr

namespace AdminHeartbeat

def encode (_ : AdminHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (AdminHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : AdminHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : AdminHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end AdminHeartbeat

/-- Admin Login: 1 bytes -/
structure AdminLogin where
  heartBtInt : BitVec 8
  deriving DecidableEq, Repr

namespace AdminLogin

def encode (message : AdminLogin) : List UInt8 :=
  encodeUInt 1 message.heartBtInt

def decode (bytes : List UInt8) : Option (AdminLogin × List UInt8) := do
  let (heartBtInt, bytes) ← decodeUInt 1 bytes
  pure ({ heartBtInt }, bytes)

@[simp] theorem encode_length (message : AdminLogin) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : AdminLogin) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdminLogin) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AdminLogin

/-- Admin Logout: 100 bytes -/
structure AdminLogout where
  text : Alpha 100
  deriving DecidableEq, Repr

namespace AdminLogout

def encode (message : AdminLogout) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (AdminLogout × List UInt8) := do
  let (text, bytes) ← Alpha.decode 100 bytes
  pure ({ text }, bytes)

@[simp] theorem encode_length (message : AdminLogout) : (encode message).length = 100 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : AdminLogout) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdminLogout) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end AdminLogout

/-- Maturity Month Year: 5 bytes -/
structure MaturityMonthYear where
  year : BitVec 16
  month : BitVec 8
  day : BitVec 8
  week : BitVec 8
  deriving DecidableEq, Repr

namespace MaturityMonthYear

def encode (message : MaturityMonthYear) : List UInt8 :=
  encodeUIntLE 2 message.year
    ++ (encodeUInt 1 message.month
    ++ (encodeUInt 1 message.day
    ++ (encodeUInt 1 message.week)))

def decode (bytes : List UInt8) : Option (MaturityMonthYear × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 2 bytes
  let (month, bytes) ← decodeUInt 1 bytes
  let (day, bytes) ← decodeUInt 1 bytes
  let (week, bytes) ← decodeUInt 1 bytes
  pure ({ year, month, day, week }, bytes)

@[simp] theorem encode_length (message : MaturityMonthYear) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MaturityMonthYear) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaturityMonthYear) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MaturityMonthYear

/-- Events Group: 9 bytes -/
structure EventsGroup where
  eventType : BitVec 8
  eventTime : BitVec 64
  deriving DecidableEq, Repr

namespace EventsGroup

def encode (message : EventsGroup) : List UInt8 :=
  encodeUInt 1 message.eventType
    ++ (encodeUIntLE 8 message.eventTime)

def decode (bytes : List UInt8) : Option (EventsGroup × List UInt8) := do
  let (eventType, bytes) ← decodeUInt 1 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ eventType, eventTime }, bytes)

@[simp] theorem encode_length (message : EventsGroup) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : EventsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EventsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EventsGroup

/-- Events Groups -/
structure EventsGroups where
  blockLength : BitVec 16
  eventsGroup : Bounded 1 EventsGroup
  deriving DecidableEq, Repr

namespace EventsGroups

def encode (message : EventsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.eventsGroup.val.length)
    ++ (encodeMany EventsGroup.encode message.eventsGroup.val))

def decode (bytes : List UInt8) : Option (EventsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (eventsGroup_, bytes) ← decodeMany EventsGroup.decode numInGroup.toNat bytes
  if fits_eventsGroup : eventsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, eventsGroup := ⟨eventsGroup_, fits_eventsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : EventsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EventsGroups) : (encode message).length ≤ 2298 := by
  have bound_eventsGroup := message.eventsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const EventsGroup.encode 9 EventsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : EventsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 EventsGroup.encode EventsGroup.decode EventsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.eventsGroup.length_lt]
  rfl

end EventsGroups

/-- Feed Types Group: 4 bytes -/
structure FeedTypesGroup where
  mdFeedType : Alpha 3
  marketDepth : BitVec 8
  deriving DecidableEq, Repr

namespace FeedTypesGroup

def encode (message : FeedTypesGroup) : List UInt8 :=
  Alpha.encode message.mdFeedType
    ++ (encodeUInt 1 message.marketDepth)

def decode (bytes : List UInt8) : Option (FeedTypesGroup × List UInt8) := do
  let (mdFeedType, bytes) ← Alpha.decode 3 bytes
  let (marketDepth, bytes) ← decodeUInt 1 bytes
  pure ({ mdFeedType, marketDepth }, bytes)

@[simp] theorem encode_length (message : FeedTypesGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FeedTypesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FeedTypesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FeedTypesGroup

/-- Feed Types Groups -/
structure FeedTypesGroups where
  blockLength : BitVec 16
  feedTypesGroup : Bounded 1 FeedTypesGroup
  deriving DecidableEq, Repr

namespace FeedTypesGroups

def encode (message : FeedTypesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.feedTypesGroup.val.length)
    ++ (encodeMany FeedTypesGroup.encode message.feedTypesGroup.val))

def decode (bytes : List UInt8) : Option (FeedTypesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (feedTypesGroup_, bytes) ← decodeMany FeedTypesGroup.decode numInGroup.toNat bytes
  if fits_feedTypesGroup : feedTypesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, feedTypesGroup := ⟨feedTypesGroup_, fits_feedTypesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : FeedTypesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FeedTypesGroups) : (encode message).length ≤ 1023 := by
  have bound_feedTypesGroup := message.feedTypesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const FeedTypesGroup.encode 4 FeedTypesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : FeedTypesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 FeedTypesGroup.encode FeedTypesGroup.decode FeedTypesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.feedTypesGroup.length_lt]
  rfl

end FeedTypesGroups

/-- Inst Attrib Group: 4 bytes -/
structure InstAttribGroup where
  instAttribValue : BitVec 32
  deriving DecidableEq, Repr

namespace InstAttribGroup

def encode (message : InstAttribGroup) : List UInt8 :=
  encodeUIntLE 4 message.instAttribValue

def decode (bytes : List UInt8) : Option (InstAttribGroup × List UInt8) := do
  let (instAttribValue, bytes) ← decodeUIntLE 4 bytes
  pure ({ instAttribValue }, bytes)

@[simp] theorem encode_length (message : InstAttribGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : InstAttribGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstAttribGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InstAttribGroup

/-- Inst Attrib Groups -/
structure InstAttribGroups where
  blockLength : BitVec 16
  instAttribGroup : Bounded 1 InstAttribGroup
  deriving DecidableEq, Repr

namespace InstAttribGroups

def encode (message : InstAttribGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instAttribGroup.val.length)
    ++ (encodeMany InstAttribGroup.encode message.instAttribGroup.val))

def decode (bytes : List UInt8) : Option (InstAttribGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (instAttribGroup_, bytes) ← decodeMany InstAttribGroup.decode numInGroup.toNat bytes
  if fits_instAttribGroup : instAttribGroup_.length < 256 ^ 1 then
    pure ({ blockLength, instAttribGroup := ⟨instAttribGroup_, fits_instAttribGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : InstAttribGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InstAttribGroups) : (encode message).length ≤ 1023 := by
  have bound_instAttribGroup := message.instAttribGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const InstAttribGroup.encode 4 InstAttribGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : InstAttribGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 InstAttribGroup.encode InstAttribGroup.decode InstAttribGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.instAttribGroup.length_lt]
  rfl

end InstAttribGroups

/-- Lot Type Rules Group: 5 bytes -/
structure LotTypeRulesGroup where
  lotType : BitVec 8
  minLotSize : BitVec 32
  deriving DecidableEq, Repr

namespace LotTypeRulesGroup

def encode (message : LotTypeRulesGroup) : List UInt8 :=
  encodeUInt 1 message.lotType
    ++ (encodeUIntLE 4 message.minLotSize)

def decode (bytes : List UInt8) : Option (LotTypeRulesGroup × List UInt8) := do
  let (lotType, bytes) ← decodeUInt 1 bytes
  let (minLotSize, bytes) ← decodeUIntLE 4 bytes
  pure ({ lotType, minLotSize }, bytes)

@[simp] theorem encode_length (message : LotTypeRulesGroup) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LotTypeRulesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LotTypeRulesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LotTypeRulesGroup

/-- Lot Type Rules Groups -/
structure LotTypeRulesGroups where
  blockLength : BitVec 16
  lotTypeRulesGroup : Bounded 1 LotTypeRulesGroup
  deriving DecidableEq, Repr

namespace LotTypeRulesGroups

def encode (message : LotTypeRulesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.lotTypeRulesGroup.val.length)
    ++ (encodeMany LotTypeRulesGroup.encode message.lotTypeRulesGroup.val))

def decode (bytes : List UInt8) : Option (LotTypeRulesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (lotTypeRulesGroup_, bytes) ← decodeMany LotTypeRulesGroup.decode numInGroup.toNat bytes
  if fits_lotTypeRulesGroup : lotTypeRulesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, lotTypeRulesGroup := ⟨lotTypeRulesGroup_, fits_lotTypeRulesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LotTypeRulesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LotTypeRulesGroups) : (encode message).length ≤ 1278 := by
  have bound_lotTypeRulesGroup := message.lotTypeRulesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const LotTypeRulesGroup.encode 5 LotTypeRulesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LotTypeRulesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LotTypeRulesGroup.encode LotTypeRulesGroup.decode LotTypeRulesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.lotTypeRulesGroup.length_lt]
  rfl

end LotTypeRulesGroups

/-- Md Instrument Definition Future -/
structure MdInstrumentDefinitionFuture where
  matchEventIndicator : BitVec 8
  totNumReportsOptional : BitVec 32
  securityUpdateAction : SecurityUpdateAction
  lastUpdateTime : BitVec 64
  mdSecurityTradingStatus : BitVec 8
  applId : BitVec 16
  marketSegmentId : BitVec 8
  underlyingProduct : BitVec 8
  securityExchange : Alpha 4
  securityGroup : Alpha 6
  asset : Alpha 6
  symbol : Alpha 20
  securityId : BitVec 32
  securityType : Alpha 6
  cfiCode : Alpha 6
  maturityMonthYear : MaturityMonthYear
  currency : Alpha 3
  settlCurrency : Alpha 3
  matchAlgorithm : Alpha 1
  minTradeVol : BitVec 32
  maxTradeVol : BitVec 32
  minPriceIncrement : BitVec 64
  displayFactor : BitVec 64
  mainFraction : BitVec 8
  subFraction : BitVec 8
  priceDisplayFormat : BitVec 8
  unitOfMeasure : Alpha 30
  unitOfMeasureQty : BitVec 64
  tradingReferencePrice : BitVec 64
  settlPriceType : BitVec 8
  openInterestQty : BitVec 32
  clearedVolume : BitVec 32
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  decayQuantity : BitVec 32
  decayStartDate : BitVec 16
  originalContractSize : BitVec 32
  contractMultiplier : BitVec 32
  contractMultiplierUnit : BitVec 8
  flowScheduleType : BitVec 8
  minPriceIncrementAmount : BitVec 64
  userDefinedInstrument : Alpha 1
  eventsGroups : EventsGroups
  feedTypesGroups : FeedTypesGroups
  instAttribGroups : InstAttribGroups
  lotTypeRulesGroups : LotTypeRulesGroups
  deriving DecidableEq, Repr

namespace MdInstrumentDefinitionFuture

def encode (message : MdInstrumentDefinitionFuture) : List UInt8 :=
  encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUIntLE 4 message.totNumReportsOptional
    ++ (SecurityUpdateAction.encode message.securityUpdateAction
    ++ (encodeUIntLE 8 message.lastUpdateTime
    ++ (encodeUInt 1 message.mdSecurityTradingStatus
    ++ (encodeUIntLE 2 message.applId
    ++ (encodeUInt 1 message.marketSegmentId
    ++ (encodeUInt 1 message.underlyingProduct
    ++ (Alpha.encode message.securityExchange
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.asset
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.securityId
    ++ (Alpha.encode message.securityType
    ++ (Alpha.encode message.cfiCode
    ++ (MaturityMonthYear.encode message.maturityMonthYear
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.settlCurrency
    ++ (Alpha.encode message.matchAlgorithm
    ++ (encodeUIntLE 4 message.minTradeVol
    ++ (encodeUIntLE 4 message.maxTradeVol
    ++ (encodeUIntLE 8 message.minPriceIncrement
    ++ (encodeUIntLE 8 message.displayFactor
    ++ (encodeUInt 1 message.mainFraction
    ++ (encodeUInt 1 message.subFraction
    ++ (encodeUInt 1 message.priceDisplayFormat
    ++ (Alpha.encode message.unitOfMeasure
    ++ (encodeUIntLE 8 message.unitOfMeasureQty
    ++ (encodeUIntLE 8 message.tradingReferencePrice
    ++ (encodeUIntLE 1 message.settlPriceType
    ++ (encodeUIntLE 4 message.openInterestQty
    ++ (encodeUIntLE 4 message.clearedVolume
    ++ (encodeUIntLE 8 message.highLimitPrice
    ++ (encodeUIntLE 8 message.lowLimitPrice
    ++ (encodeUIntLE 8 message.maxPriceVariation
    ++ (encodeUIntLE 4 message.decayQuantity
    ++ (encodeUIntLE 2 message.decayStartDate
    ++ (encodeUIntLE 4 message.originalContractSize
    ++ (encodeUIntLE 4 message.contractMultiplier
    ++ (encodeUInt 1 message.contractMultiplierUnit
    ++ (encodeUInt 1 message.flowScheduleType
    ++ (encodeUIntLE 8 message.minPriceIncrementAmount
    ++ (Alpha.encode message.userDefinedInstrument
    ++ (EventsGroups.encode message.eventsGroups
    ++ (FeedTypesGroups.encode message.feedTypesGroups
    ++ (InstAttribGroups.encode message.instAttribGroups
    ++ (LotTypeRulesGroups.encode message.lotTypeRulesGroups))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MdInstrumentDefinitionFuture × List UInt8) := do
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (totNumReportsOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityUpdateAction, bytes) ← SecurityUpdateAction.decode bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (mdSecurityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (applId, bytes) ← decodeUIntLE 2 bytes
  let (marketSegmentId, bytes) ← decodeUInt 1 bytes
  let (underlyingProduct, bytes) ← decodeUInt 1 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  let (asset, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (securityType, bytes) ← Alpha.decode 6 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (settlCurrency, bytes) ← Alpha.decode 3 bytes
  let (matchAlgorithm, bytes) ← Alpha.decode 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (maxTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (minPriceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (displayFactor, bytes) ← decodeUIntLE 8 bytes
  let (mainFraction, bytes) ← decodeUInt 1 bytes
  let (subFraction, bytes) ← decodeUInt 1 bytes
  let (priceDisplayFormat, bytes) ← decodeUInt 1 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 30 bytes
  let (unitOfMeasureQty, bytes) ← decodeUIntLE 8 bytes
  let (tradingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (openInterestQty, bytes) ← decodeUIntLE 4 bytes
  let (clearedVolume, bytes) ← decodeUIntLE 4 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (decayQuantity, bytes) ← decodeUIntLE 4 bytes
  let (decayStartDate, bytes) ← decodeUIntLE 2 bytes
  let (originalContractSize, bytes) ← decodeUIntLE 4 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 4 bytes
  let (contractMultiplierUnit, bytes) ← decodeUInt 1 bytes
  let (flowScheduleType, bytes) ← decodeUInt 1 bytes
  let (minPriceIncrementAmount, bytes) ← decodeUIntLE 8 bytes
  let (userDefinedInstrument, bytes) ← Alpha.decode 1 bytes
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  let (feedTypesGroups, bytes) ← FeedTypesGroups.decode bytes
  let (instAttribGroups, bytes) ← InstAttribGroups.decode bytes
  let (lotTypeRulesGroups, bytes) ← LotTypeRulesGroups.decode bytes
  pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, maturityMonthYear, currency, settlCurrency, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrement, displayFactor, mainFraction, subFraction, priceDisplayFormat, unitOfMeasure, unitOfMeasureQty, tradingReferencePrice, settlPriceType, openInterestQty, clearedVolume, highLimitPrice, lowLimitPrice, maxPriceVariation, decayQuantity, decayStartDate, originalContractSize, contractMultiplier, contractMultiplierUnit, flowScheduleType, minPriceIncrementAmount, userDefinedInstrument, eventsGroups, feedTypesGroups, instAttribGroups, lotTypeRulesGroups }, bytes)

theorem encode_length_pos (message : MdInstrumentDefinitionFuture) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdInstrumentDefinitionFuture) : (encode message).length ≤ 5836 := by
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  have bound_feedTypesGroups := FeedTypesGroups.encode_length_le message.feedTypesGroups
  have bound_instAttribGroups := InstAttribGroups.encode_length_le message.instAttribGroups
  have bound_lotTypeRulesGroups := LotTypeRulesGroups.encode_length_le message.lotTypeRulesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SecurityUpdateAction.encode_length, encodeUInt_length, Alpha.encode_length, MaturityMonthYear.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MdInstrumentDefinitionFuture) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityUpdateAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaturityMonthYear.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FeedTypesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstAttribGroups.decode_encode, some_bind]
  dsimp only
  rw [LotTypeRulesGroups.decode_encode, some_bind]
  rfl

end MdInstrumentDefinitionFuture

/-- Legacy Legs Group: 18 bytes -/
structure LegacyLegsGroup where
  legSecurityId : BitVec 32
  legSide : BitVec 8
  legRatioQty : BitVec 8
  legPrice : BitVec 64
  legOptionDelta : BitVec 32
  deriving DecidableEq, Repr

namespace LegacyLegsGroup

def encode (message : LegacyLegsGroup) : List UInt8 :=
  encodeUIntLE 4 message.legSecurityId
    ++ (encodeUInt 1 message.legSide
    ++ (encodeUInt 1 message.legRatioQty
    ++ (encodeUIntLE 8 message.legPrice
    ++ (encodeUIntLE 4 message.legOptionDelta))))

def decode (bytes : List UInt8) : Option (LegacyLegsGroup × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (legRatioQty, bytes) ← decodeUInt 1 bytes
  let (legPrice, bytes) ← decodeUIntLE 8 bytes
  let (legOptionDelta, bytes) ← decodeUIntLE 4 bytes
  pure ({ legSecurityId, legSide, legRatioQty, legPrice, legOptionDelta }, bytes)

@[simp] theorem encode_length (message : LegacyLegsGroup) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LegacyLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegacyLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LegacyLegsGroup

/-- Legacy Legs Groups -/
structure LegacyLegsGroups where
  blockLength : BitVec 16
  legacyLegsGroup : Bounded 1 LegacyLegsGroup
  deriving DecidableEq, Repr

namespace LegacyLegsGroups

def encode (message : LegacyLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legacyLegsGroup.val.length)
    ++ (encodeMany LegacyLegsGroup.encode message.legacyLegsGroup.val))

def decode (bytes : List UInt8) : Option (LegacyLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (legacyLegsGroup_, bytes) ← decodeMany LegacyLegsGroup.decode numInGroup.toNat bytes
  if fits_legacyLegsGroup : legacyLegsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, legacyLegsGroup := ⟨legacyLegsGroup_, fits_legacyLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LegacyLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LegacyLegsGroups) : (encode message).length ≤ 4593 := by
  have bound_legacyLegsGroup := message.legacyLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const LegacyLegsGroup.encode 18 LegacyLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LegacyLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegacyLegsGroup.encode LegacyLegsGroup.decode LegacyLegsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legacyLegsGroup.length_lt]
  rfl

end LegacyLegsGroups

/-- Md Instrument Definition Spread -/
structure MdInstrumentDefinitionSpread where
  matchEventIndicator : BitVec 8
  totNumReportsOptional : BitVec 32
  securityUpdateAction : SecurityUpdateAction
  lastUpdateTime : BitVec 64
  mdSecurityTradingStatus : BitVec 8
  applId : BitVec 16
  marketSegmentId : BitVec 8
  underlyingProductOptional : BitVec 8
  securityExchange : Alpha 4
  securityGroup : Alpha 6
  asset : Alpha 6
  symbol : Alpha 20
  securityId : BitVec 32
  securityType : Alpha 6
  cfiCode : Alpha 6
  maturityMonthYear : MaturityMonthYear
  currency : Alpha 3
  securitySubType : Alpha 5
  userDefinedInstrument : Alpha 1
  matchAlgorithm : Alpha 1
  minTradeVol : BitVec 32
  maxTradeVol : BitVec 32
  minPriceIncrement : BitVec 64
  displayFactor : BitVec 64
  priceDisplayFormat : BitVec 8
  priceRatio : BitVec 64
  tickRule : BitVec 8
  unitOfMeasure : Alpha 30
  tradingReferencePrice : BitVec 64
  settlPriceType : BitVec 8
  openInterestQty : BitVec 32
  clearedVolume : BitVec 32
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  mainFraction : BitVec 8
  subFraction : BitVec 8
  eventsGroups : EventsGroups
  feedTypesGroups : FeedTypesGroups
  instAttribGroups : InstAttribGroups
  lotTypeRulesGroups : LotTypeRulesGroups
  legacyLegsGroups : LegacyLegsGroups
  deriving DecidableEq, Repr

namespace MdInstrumentDefinitionSpread

def encode (message : MdInstrumentDefinitionSpread) : List UInt8 :=
  encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUIntLE 4 message.totNumReportsOptional
    ++ (SecurityUpdateAction.encode message.securityUpdateAction
    ++ (encodeUIntLE 8 message.lastUpdateTime
    ++ (encodeUInt 1 message.mdSecurityTradingStatus
    ++ (encodeUIntLE 2 message.applId
    ++ (encodeUInt 1 message.marketSegmentId
    ++ (encodeUInt 1 message.underlyingProductOptional
    ++ (Alpha.encode message.securityExchange
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.asset
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.securityId
    ++ (Alpha.encode message.securityType
    ++ (Alpha.encode message.cfiCode
    ++ (MaturityMonthYear.encode message.maturityMonthYear
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.securitySubType
    ++ (Alpha.encode message.userDefinedInstrument
    ++ (Alpha.encode message.matchAlgorithm
    ++ (encodeUIntLE 4 message.minTradeVol
    ++ (encodeUIntLE 4 message.maxTradeVol
    ++ (encodeUIntLE 8 message.minPriceIncrement
    ++ (encodeUIntLE 8 message.displayFactor
    ++ (encodeUInt 1 message.priceDisplayFormat
    ++ (encodeUIntLE 8 message.priceRatio
    ++ (encodeUInt 1 message.tickRule
    ++ (Alpha.encode message.unitOfMeasure
    ++ (encodeUIntLE 8 message.tradingReferencePrice
    ++ (encodeUIntLE 1 message.settlPriceType
    ++ (encodeUIntLE 4 message.openInterestQty
    ++ (encodeUIntLE 4 message.clearedVolume
    ++ (encodeUIntLE 8 message.highLimitPrice
    ++ (encodeUIntLE 8 message.lowLimitPrice
    ++ (encodeUIntLE 8 message.maxPriceVariation
    ++ (encodeUInt 1 message.mainFraction
    ++ (encodeUInt 1 message.subFraction
    ++ (EventsGroups.encode message.eventsGroups
    ++ (FeedTypesGroups.encode message.feedTypesGroups
    ++ (InstAttribGroups.encode message.instAttribGroups
    ++ (LotTypeRulesGroups.encode message.lotTypeRulesGroups
    ++ (LegacyLegsGroups.encode message.legacyLegsGroups)))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MdInstrumentDefinitionSpread × List UInt8) := do
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (totNumReportsOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityUpdateAction, bytes) ← SecurityUpdateAction.decode bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (mdSecurityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (applId, bytes) ← decodeUIntLE 2 bytes
  let (marketSegmentId, bytes) ← decodeUInt 1 bytes
  let (underlyingProductOptional, bytes) ← decodeUInt 1 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  let (asset, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (securityType, bytes) ← Alpha.decode 6 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (securitySubType, bytes) ← Alpha.decode 5 bytes
  let (userDefinedInstrument, bytes) ← Alpha.decode 1 bytes
  let (matchAlgorithm, bytes) ← Alpha.decode 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (maxTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (minPriceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (displayFactor, bytes) ← decodeUIntLE 8 bytes
  let (priceDisplayFormat, bytes) ← decodeUInt 1 bytes
  let (priceRatio, bytes) ← decodeUIntLE 8 bytes
  let (tickRule, bytes) ← decodeUInt 1 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 30 bytes
  let (tradingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (openInterestQty, bytes) ← decodeUIntLE 4 bytes
  let (clearedVolume, bytes) ← decodeUIntLE 4 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (mainFraction, bytes) ← decodeUInt 1 bytes
  let (subFraction, bytes) ← decodeUInt 1 bytes
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  let (feedTypesGroups, bytes) ← FeedTypesGroups.decode bytes
  let (instAttribGroups, bytes) ← InstAttribGroups.decode bytes
  let (lotTypeRulesGroups, bytes) ← LotTypeRulesGroups.decode bytes
  let (legacyLegsGroups, bytes) ← LegacyLegsGroups.decode bytes
  pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProductOptional, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, maturityMonthYear, currency, securitySubType, userDefinedInstrument, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrement, displayFactor, priceDisplayFormat, priceRatio, tickRule, unitOfMeasure, tradingReferencePrice, settlPriceType, openInterestQty, clearedVolume, highLimitPrice, lowLimitPrice, maxPriceVariation, mainFraction, subFraction, eventsGroups, feedTypesGroups, instAttribGroups, lotTypeRulesGroups, legacyLegsGroups }, bytes)

theorem encode_length_pos (message : MdInstrumentDefinitionSpread) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdInstrumentDefinitionSpread) : (encode message).length ≤ 10408 := by
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  have bound_feedTypesGroups := FeedTypesGroups.encode_length_le message.feedTypesGroups
  have bound_instAttribGroups := InstAttribGroups.encode_length_le message.instAttribGroups
  have bound_lotTypeRulesGroups := LotTypeRulesGroups.encode_length_le message.lotTypeRulesGroups
  have bound_legacyLegsGroups := LegacyLegsGroups.encode_length_le message.legacyLegsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SecurityUpdateAction.encode_length, encodeUInt_length, Alpha.encode_length, MaturityMonthYear.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MdInstrumentDefinitionSpread) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityUpdateAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaturityMonthYear.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, EventsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FeedTypesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstAttribGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LotTypeRulesGroups.decode_encode, some_bind]
  dsimp only
  rw [LegacyLegsGroups.decode_encode, some_bind]
  rfl

end MdInstrumentDefinitionSpread

/-- Security Status: 30 bytes -/
structure SecurityStatus where
  transactTime : BitVec 64
  securityGroup : Alpha 6
  asset : Alpha 6
  securityIdOptional : BitVec 32
  tradeDate : BitVec 16
  matchEventIndicator : BitVec 8
  securityTradingStatus : BitVec 8
  haltReason : BitVec 8
  securityTradingEvent : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityStatus

def encode (message : SecurityStatus) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.asset
    ++ (encodeUIntLE 4 message.securityIdOptional
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUInt 1 message.securityTradingStatus
    ++ (encodeUInt 1 message.haltReason
    ++ (encodeUInt 1 message.securityTradingEvent))))))))

def decode (bytes : List UInt8) : Option (SecurityStatus × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  let (asset, bytes) ← Alpha.decode 6 bytes
  let (securityIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (haltReason, bytes) ← decodeUInt 1 bytes
  let (securityTradingEvent, bytes) ← decodeUInt 1 bytes
  pure ({ transactTime, securityGroup, asset, securityIdOptional, tradeDate, matchEventIndicator, securityTradingStatus, haltReason, securityTradingEvent }, bytes)

@[simp] theorem encode_length (message : SecurityStatus) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatus) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecurityStatus

/-- Incremental Refresh Book Group: 32 bytes -/
structure IncrementalRefreshBookGroup where
  mdEntryPxOptional : BitVec 64
  mdEntrySizeOptional : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  numberOfOrders : BitVec 32
  mdPriceLevel : BitVec 8
  mdUpdateAction : BitVec 8
  mdEntryTypeBook : MdEntryTypeBook
  padding5 : Alpha 5
  deriving DecidableEq, Repr

namespace IncrementalRefreshBookGroup

def encode (message : IncrementalRefreshBookGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxOptional
    ++ (encodeUIntLE 4 message.mdEntrySizeOptional
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUIntLE 4 message.numberOfOrders
    ++ (encodeUInt 1 message.mdPriceLevel
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (MdEntryTypeBook.encode message.mdEntryTypeBook
    ++ (Alpha.encode message.padding5))))))))

def decode (bytes : List UInt8) : Option (IncrementalRefreshBookGroup × List UInt8) := do
  let (mdEntryPxOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (mdPriceLevel, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryTypeBook, bytes) ← MdEntryTypeBook.decode bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  pure ({ mdEntryPxOptional, mdEntrySizeOptional, securityId, rptSeq, numberOfOrders, mdPriceLevel, mdUpdateAction, mdEntryTypeBook, padding5 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshBookGroup) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryTypeBook.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshBookGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshBookGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MdEntryTypeBook.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IncrementalRefreshBookGroup

/-- Incremental Refresh Book Groups -/
structure IncrementalRefreshBookGroups where
  blockLength : BitVec 16
  incrementalRefreshBookGroup : Bounded 1 IncrementalRefreshBookGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshBookGroups

def encode (message : IncrementalRefreshBookGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshBookGroup.val.length)
    ++ (encodeMany IncrementalRefreshBookGroup.encode message.incrementalRefreshBookGroup.val))

def decode (bytes : List UInt8) : Option (IncrementalRefreshBookGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshBookGroup_, bytes) ← decodeMany IncrementalRefreshBookGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshBookGroup : incrementalRefreshBookGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshBookGroup := ⟨incrementalRefreshBookGroup_, fits_incrementalRefreshBookGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshBookGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshBookGroups) : (encode message).length ≤ 8163 := by
  have bound_incrementalRefreshBookGroup := message.incrementalRefreshBookGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshBookGroup.encode 32 IncrementalRefreshBookGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshBookGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshBookGroup.encode IncrementalRefreshBookGroup.decode IncrementalRefreshBookGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.incrementalRefreshBookGroup.length_lt]
  rfl

end IncrementalRefreshBookGroups

/-- Md Incremental Refresh Book -/
structure MdIncrementalRefreshBook where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshBookGroups : IncrementalRefreshBookGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshBook

def encode (message : MdIncrementalRefreshBook) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.padding2
    ++ (IncrementalRefreshBookGroups.encode message.incrementalRefreshBookGroups)))

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshBook × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshBookGroups, bytes) ← IncrementalRefreshBookGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshBookGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshBook) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshBook) : (encode message).length ≤ 8174 := by
  have bound_incrementalRefreshBookGroups := IncrementalRefreshBookGroups.encode_length_le message.incrementalRefreshBookGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshBook) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [IncrementalRefreshBookGroups.decode_encode, some_bind]
  rfl

end MdIncrementalRefreshBook

/-- Incremental Refresh Daily Statistics Group: 32 bytes -/
structure IncrementalRefreshDailyStatisticsGroup where
  mdEntryPxOptional : BitVec 64
  mdEntrySizeOptional : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  tradingReferenceDate : BitVec 16
  settlPriceType : BitVec 8
  mdUpdateAction : BitVec 8
  mdEntryTypeDailyStatistics : MdEntryTypeDailyStatistics
  padding7 : Alpha 7
  deriving DecidableEq, Repr

namespace IncrementalRefreshDailyStatisticsGroup

def encode (message : IncrementalRefreshDailyStatisticsGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxOptional
    ++ (encodeUIntLE 4 message.mdEntrySizeOptional
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUIntLE 2 message.tradingReferenceDate
    ++ (encodeUIntLE 1 message.settlPriceType
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (MdEntryTypeDailyStatistics.encode message.mdEntryTypeDailyStatistics
    ++ (Alpha.encode message.padding7))))))))

def decode (bytes : List UInt8) : Option (IncrementalRefreshDailyStatisticsGroup × List UInt8) := do
  let (mdEntryPxOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryTypeDailyStatistics, bytes) ← MdEntryTypeDailyStatistics.decode bytes
  let (padding7, bytes) ← Alpha.decode 7 bytes
  pure ({ mdEntryPxOptional, mdEntrySizeOptional, securityId, rptSeq, tradingReferenceDate, settlPriceType, mdUpdateAction, mdEntryTypeDailyStatistics, padding7 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshDailyStatisticsGroup) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryTypeDailyStatistics.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshDailyStatisticsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshDailyStatisticsGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MdEntryTypeDailyStatistics.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IncrementalRefreshDailyStatisticsGroup

/-- Incremental Refresh Daily Statistics Groups -/
structure IncrementalRefreshDailyStatisticsGroups where
  blockLength : BitVec 16
  incrementalRefreshDailyStatisticsGroup : Bounded 1 IncrementalRefreshDailyStatisticsGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshDailyStatisticsGroups

def encode (message : IncrementalRefreshDailyStatisticsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshDailyStatisticsGroup.val.length)
    ++ (encodeMany IncrementalRefreshDailyStatisticsGroup.encode message.incrementalRefreshDailyStatisticsGroup.val))

def decode (bytes : List UInt8) : Option (IncrementalRefreshDailyStatisticsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshDailyStatisticsGroup_, bytes) ← decodeMany IncrementalRefreshDailyStatisticsGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshDailyStatisticsGroup : incrementalRefreshDailyStatisticsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshDailyStatisticsGroup := ⟨incrementalRefreshDailyStatisticsGroup_, fits_incrementalRefreshDailyStatisticsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshDailyStatisticsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshDailyStatisticsGroups) : (encode message).length ≤ 8163 := by
  have bound_incrementalRefreshDailyStatisticsGroup := message.incrementalRefreshDailyStatisticsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshDailyStatisticsGroup.encode 32 IncrementalRefreshDailyStatisticsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshDailyStatisticsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshDailyStatisticsGroup.encode IncrementalRefreshDailyStatisticsGroup.decode IncrementalRefreshDailyStatisticsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.incrementalRefreshDailyStatisticsGroup.length_lt]
  rfl

end IncrementalRefreshDailyStatisticsGroups

/-- Md Incremental Refresh Daily Statistics -/
structure MdIncrementalRefreshDailyStatistics where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshDailyStatisticsGroups : IncrementalRefreshDailyStatisticsGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshDailyStatistics

def encode (message : MdIncrementalRefreshDailyStatistics) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.padding2
    ++ (IncrementalRefreshDailyStatisticsGroups.encode message.incrementalRefreshDailyStatisticsGroups)))

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshDailyStatistics × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshDailyStatisticsGroups, bytes) ← IncrementalRefreshDailyStatisticsGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshDailyStatisticsGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshDailyStatistics) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshDailyStatistics) : (encode message).length ≤ 8174 := by
  have bound_incrementalRefreshDailyStatisticsGroups := IncrementalRefreshDailyStatisticsGroups.encode_length_le message.incrementalRefreshDailyStatisticsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshDailyStatistics) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [IncrementalRefreshDailyStatisticsGroups.decode_encode, some_bind]
  rfl

end MdIncrementalRefreshDailyStatistics

/-- Incremental Refresh Limits Banding Group: 32 bytes -/
structure IncrementalRefreshLimitsBandingGroup where
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  securityId : BitVec 32
  rptSeq : BitVec 32
  deriving DecidableEq, Repr

namespace IncrementalRefreshLimitsBandingGroup

def encode (message : IncrementalRefreshLimitsBandingGroup) : List UInt8 :=
  encodeUIntLE 8 message.highLimitPrice
    ++ (encodeUIntLE 8 message.lowLimitPrice
    ++ (encodeUIntLE 8 message.maxPriceVariation
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.rptSeq))))

def decode (bytes : List UInt8) : Option (IncrementalRefreshLimitsBandingGroup × List UInt8) := do
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  pure ({ highLimitPrice, lowLimitPrice, maxPriceVariation, securityId, rptSeq }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshLimitsBandingGroup) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : IncrementalRefreshLimitsBandingGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshLimitsBandingGroup) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IncrementalRefreshLimitsBandingGroup

/-- Incremental Refresh Limits Banding Groups -/
structure IncrementalRefreshLimitsBandingGroups where
  blockLength : BitVec 16
  incrementalRefreshLimitsBandingGroup : Bounded 1 IncrementalRefreshLimitsBandingGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshLimitsBandingGroups

def encode (message : IncrementalRefreshLimitsBandingGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshLimitsBandingGroup.val.length)
    ++ (encodeMany IncrementalRefreshLimitsBandingGroup.encode message.incrementalRefreshLimitsBandingGroup.val))

def decode (bytes : List UInt8) : Option (IncrementalRefreshLimitsBandingGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshLimitsBandingGroup_, bytes) ← decodeMany IncrementalRefreshLimitsBandingGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshLimitsBandingGroup : incrementalRefreshLimitsBandingGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshLimitsBandingGroup := ⟨incrementalRefreshLimitsBandingGroup_, fits_incrementalRefreshLimitsBandingGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshLimitsBandingGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshLimitsBandingGroups) : (encode message).length ≤ 8163 := by
  have bound_incrementalRefreshLimitsBandingGroup := message.incrementalRefreshLimitsBandingGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshLimitsBandingGroup.encode 32 IncrementalRefreshLimitsBandingGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshLimitsBandingGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshLimitsBandingGroup.encode IncrementalRefreshLimitsBandingGroup.decode IncrementalRefreshLimitsBandingGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.incrementalRefreshLimitsBandingGroup.length_lt]
  rfl

end IncrementalRefreshLimitsBandingGroups

/-- Md Incremental Refresh Limits Banding -/
structure MdIncrementalRefreshLimitsBanding where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshLimitsBandingGroups : IncrementalRefreshLimitsBandingGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshLimitsBanding

def encode (message : MdIncrementalRefreshLimitsBanding) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.padding2
    ++ (IncrementalRefreshLimitsBandingGroups.encode message.incrementalRefreshLimitsBandingGroups)))

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshLimitsBanding × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshLimitsBandingGroups, bytes) ← IncrementalRefreshLimitsBandingGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshLimitsBandingGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshLimitsBanding) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshLimitsBanding) : (encode message).length ≤ 8174 := by
  have bound_incrementalRefreshLimitsBandingGroups := IncrementalRefreshLimitsBandingGroups.encode_length_le message.incrementalRefreshLimitsBandingGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshLimitsBanding) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [IncrementalRefreshLimitsBandingGroups.decode_encode, some_bind]
  rfl

end MdIncrementalRefreshLimitsBanding

/-- Incremental Refresh Session Statistics Group: 24 bytes -/
structure IncrementalRefreshSessionStatisticsGroup where
  mdEntryPx : BitVec 64
  securityId : BitVec 32
  rptSeq : BitVec 32
  openCloseSettlFlag : BitVec 8
  mdUpdateAction : BitVec 8
  mdEntryTypeStatistics : MdEntryTypeStatistics
  padding5 : Alpha 5
  deriving DecidableEq, Repr

namespace IncrementalRefreshSessionStatisticsGroup

def encode (message : IncrementalRefreshSessionStatisticsGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPx
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUInt 1 message.openCloseSettlFlag
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (MdEntryTypeStatistics.encode message.mdEntryTypeStatistics
    ++ (Alpha.encode message.padding5))))))

def decode (bytes : List UInt8) : Option (IncrementalRefreshSessionStatisticsGroup × List UInt8) := do
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryTypeStatistics, bytes) ← MdEntryTypeStatistics.decode bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  pure ({ mdEntryPx, securityId, rptSeq, openCloseSettlFlag, mdUpdateAction, mdEntryTypeStatistics, padding5 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshSessionStatisticsGroup) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryTypeStatistics.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshSessionStatisticsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshSessionStatisticsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MdEntryTypeStatistics.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IncrementalRefreshSessionStatisticsGroup

/-- Incremental Refresh Session Statistics Groups -/
structure IncrementalRefreshSessionStatisticsGroups where
  blockLength : BitVec 16
  incrementalRefreshSessionStatisticsGroup : Bounded 1 IncrementalRefreshSessionStatisticsGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshSessionStatisticsGroups

def encode (message : IncrementalRefreshSessionStatisticsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshSessionStatisticsGroup.val.length)
    ++ (encodeMany IncrementalRefreshSessionStatisticsGroup.encode message.incrementalRefreshSessionStatisticsGroup.val))

def decode (bytes : List UInt8) : Option (IncrementalRefreshSessionStatisticsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshSessionStatisticsGroup_, bytes) ← decodeMany IncrementalRefreshSessionStatisticsGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshSessionStatisticsGroup : incrementalRefreshSessionStatisticsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshSessionStatisticsGroup := ⟨incrementalRefreshSessionStatisticsGroup_, fits_incrementalRefreshSessionStatisticsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshSessionStatisticsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshSessionStatisticsGroups) : (encode message).length ≤ 6123 := by
  have bound_incrementalRefreshSessionStatisticsGroup := message.incrementalRefreshSessionStatisticsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshSessionStatisticsGroup.encode 24 IncrementalRefreshSessionStatisticsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshSessionStatisticsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshSessionStatisticsGroup.encode IncrementalRefreshSessionStatisticsGroup.decode IncrementalRefreshSessionStatisticsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.incrementalRefreshSessionStatisticsGroup.length_lt]
  rfl

end IncrementalRefreshSessionStatisticsGroups

/-- Md Incremental Refresh Session Statistics -/
structure MdIncrementalRefreshSessionStatistics where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshSessionStatisticsGroups : IncrementalRefreshSessionStatisticsGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshSessionStatistics

def encode (message : MdIncrementalRefreshSessionStatistics) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.padding2
    ++ (IncrementalRefreshSessionStatisticsGroups.encode message.incrementalRefreshSessionStatisticsGroups)))

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshSessionStatistics × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshSessionStatisticsGroups, bytes) ← IncrementalRefreshSessionStatisticsGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshSessionStatisticsGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshSessionStatistics) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshSessionStatistics) : (encode message).length ≤ 6134 := by
  have bound_incrementalRefreshSessionStatisticsGroups := IncrementalRefreshSessionStatisticsGroups.encode_length_le message.incrementalRefreshSessionStatisticsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshSessionStatistics) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [IncrementalRefreshSessionStatisticsGroups.decode_encode, some_bind]
  rfl

end MdIncrementalRefreshSessionStatistics

/-- Incremental Refresh Trade Group: 32 bytes -/
structure IncrementalRefreshTradeGroup where
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  numberOfOrders : BitVec 32
  tradeId : BitVec 32
  aggressorSide : BitVec 8
  mdUpdateAction : BitVec 8
  padding2 : Alpha 2
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeGroup

def encode (message : IncrementalRefreshTradeGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPx
    ++ (encodeUIntLE 4 message.mdEntrySize
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUIntLE 4 message.numberOfOrders
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUInt 1 message.aggressorSide
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (Alpha.encode message.padding2))))))))

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeGroup × List UInt8) := do
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  pure ({ mdEntryPx, mdEntrySize, securityId, rptSeq, numberOfOrders, tradeId, aggressorSide, mdUpdateAction, padding2 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshTradeGroup) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshTradeGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshTradeGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IncrementalRefreshTradeGroup

/-- Incremental Refresh Trade Groups -/
structure IncrementalRefreshTradeGroups where
  blockLength : BitVec 16
  incrementalRefreshTradeGroup : Bounded 1 IncrementalRefreshTradeGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeGroups

def encode (message : IncrementalRefreshTradeGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshTradeGroup.val.length)
    ++ (encodeMany IncrementalRefreshTradeGroup.encode message.incrementalRefreshTradeGroup.val))

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTradeGroup_, bytes) ← decodeMany IncrementalRefreshTradeGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshTradeGroup : incrementalRefreshTradeGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshTradeGroup := ⟨incrementalRefreshTradeGroup_, fits_incrementalRefreshTradeGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshTradeGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshTradeGroups) : (encode message).length ≤ 8163 := by
  have bound_incrementalRefreshTradeGroup := message.incrementalRefreshTradeGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshTradeGroup.encode 32 IncrementalRefreshTradeGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshTradeGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshTradeGroup.encode IncrementalRefreshTradeGroup.decode IncrementalRefreshTradeGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.incrementalRefreshTradeGroup.length_lt]
  rfl

end IncrementalRefreshTradeGroups

/-- Md Incremental Refresh Trade -/
structure MdIncrementalRefreshTrade where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshTradeGroups : IncrementalRefreshTradeGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshTrade

def encode (message : MdIncrementalRefreshTrade) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.padding2
    ++ (IncrementalRefreshTradeGroups.encode message.incrementalRefreshTradeGroups)))

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshTrade × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshTradeGroups, bytes) ← IncrementalRefreshTradeGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshTradeGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshTrade) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshTrade) : (encode message).length ≤ 8174 := by
  have bound_incrementalRefreshTradeGroups := IncrementalRefreshTradeGroups.encode_length_le message.incrementalRefreshTradeGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshTrade) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [IncrementalRefreshTradeGroups.decode_encode, some_bind]
  rfl

end MdIncrementalRefreshTrade

/-- Incremental Refresh Volume Group: 16 bytes -/
structure IncrementalRefreshVolumeGroup where
  mdEntrySize : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  mdUpdateAction : BitVec 8
  padding3 : Alpha 3
  deriving DecidableEq, Repr

namespace IncrementalRefreshVolumeGroup

def encode (message : IncrementalRefreshVolumeGroup) : List UInt8 :=
  encodeUIntLE 4 message.mdEntrySize
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (Alpha.encode message.padding3))))

def decode (bytes : List UInt8) : Option (IncrementalRefreshVolumeGroup × List UInt8) := do
  let (mdEntrySize, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (padding3, bytes) ← Alpha.decode 3 bytes
  pure ({ mdEntrySize, securityId, rptSeq, mdUpdateAction, padding3 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshVolumeGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshVolumeGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshVolumeGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IncrementalRefreshVolumeGroup

/-- Incremental Refresh Volume Groups -/
structure IncrementalRefreshVolumeGroups where
  blockLength : BitVec 16
  incrementalRefreshVolumeGroup : Bounded 1 IncrementalRefreshVolumeGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshVolumeGroups

def encode (message : IncrementalRefreshVolumeGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshVolumeGroup.val.length)
    ++ (encodeMany IncrementalRefreshVolumeGroup.encode message.incrementalRefreshVolumeGroup.val))

def decode (bytes : List UInt8) : Option (IncrementalRefreshVolumeGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshVolumeGroup_, bytes) ← decodeMany IncrementalRefreshVolumeGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshVolumeGroup : incrementalRefreshVolumeGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshVolumeGroup := ⟨incrementalRefreshVolumeGroup_, fits_incrementalRefreshVolumeGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshVolumeGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshVolumeGroups) : (encode message).length ≤ 4083 := by
  have bound_incrementalRefreshVolumeGroup := message.incrementalRefreshVolumeGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshVolumeGroup.encode 16 IncrementalRefreshVolumeGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshVolumeGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshVolumeGroup.encode IncrementalRefreshVolumeGroup.decode IncrementalRefreshVolumeGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.incrementalRefreshVolumeGroup.length_lt]
  rfl

end IncrementalRefreshVolumeGroups

/-- Md Incremental Refresh Volume -/
structure MdIncrementalRefreshVolume where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshVolumeGroups : IncrementalRefreshVolumeGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshVolume

def encode (message : MdIncrementalRefreshVolume) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.padding2
    ++ (IncrementalRefreshVolumeGroups.encode message.incrementalRefreshVolumeGroups)))

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshVolume × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshVolumeGroups, bytes) ← IncrementalRefreshVolumeGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshVolumeGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshVolume) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshVolume) : (encode message).length ≤ 4094 := by
  have bound_incrementalRefreshVolumeGroups := IncrementalRefreshVolumeGroups.encode_length_le message.incrementalRefreshVolumeGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshVolume) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [IncrementalRefreshVolumeGroups.decode_encode, some_bind]
  rfl

end MdIncrementalRefreshVolume

/-- Snapshot Full Refresh Group: 22 bytes -/
structure SnapshotFullRefreshGroup where
  mdEntryPxOptional : BitVec 64
  mdEntrySizeOptional : BitVec 32
  numberOfOrders : BitVec 32
  mdPriceLevelOptional : BitVec 8
  tradingReferenceDate : BitVec 16
  openCloseSettlFlag : BitVec 8
  settlPriceType : BitVec 8
  mdEntryType : MdEntryType
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshGroup

def encode (message : SnapshotFullRefreshGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPxOptional
    ++ (encodeUIntLE 4 message.mdEntrySizeOptional
    ++ (encodeUIntLE 4 message.numberOfOrders
    ++ (encodeUInt 1 message.mdPriceLevelOptional
    ++ (encodeUIntLE 2 message.tradingReferenceDate
    ++ (encodeUInt 1 message.openCloseSettlFlag
    ++ (encodeUIntLE 1 message.settlPriceType
    ++ (MdEntryType.encode message.mdEntryType)))))))

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshGroup × List UInt8) := do
  let (mdEntryPxOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (mdPriceLevelOptional, bytes) ← decodeUInt 1 bytes
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  pure ({ mdEntryPxOptional, mdEntrySizeOptional, numberOfOrders, mdPriceLevelOptional, tradingReferenceDate, openCloseSettlFlag, settlPriceType, mdEntryType }, bytes)

@[simp] theorem encode_length (message : SnapshotFullRefreshGroup) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryType.encode_length]

theorem encode_length_pos (message : SnapshotFullRefreshGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotFullRefreshGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [MdEntryType.decode_encode, some_bind]
  rfl

end SnapshotFullRefreshGroup

/-- Snapshot Full Refresh Groups -/
structure SnapshotFullRefreshGroups where
  blockLength : BitVec 16
  snapshotFullRefreshGroup : Bounded 1 SnapshotFullRefreshGroup
  deriving DecidableEq, Repr

namespace SnapshotFullRefreshGroups

def encode (message : SnapshotFullRefreshGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.snapshotFullRefreshGroup.val.length)
    ++ (encodeMany SnapshotFullRefreshGroup.encode message.snapshotFullRefreshGroup.val))

def decode (bytes : List UInt8) : Option (SnapshotFullRefreshGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotFullRefreshGroup_, bytes) ← decodeMany SnapshotFullRefreshGroup.decode numInGroup.toNat bytes
  if fits_snapshotFullRefreshGroup : snapshotFullRefreshGroup_.length < 256 ^ 1 then
    pure ({ blockLength, snapshotFullRefreshGroup := ⟨snapshotFullRefreshGroup_, fits_snapshotFullRefreshGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotFullRefreshGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotFullRefreshGroups) : (encode message).length ≤ 5613 := by
  have bound_snapshotFullRefreshGroup := message.snapshotFullRefreshGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SnapshotFullRefreshGroup.encode 22 SnapshotFullRefreshGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotFullRefreshGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SnapshotFullRefreshGroup.encode SnapshotFullRefreshGroup.decode SnapshotFullRefreshGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.snapshotFullRefreshGroup.length_lt]
  rfl

end SnapshotFullRefreshGroups

/-- Snapshot Full Refresh -/
structure SnapshotFullRefresh where
  lastMsgSeqNumProcessed : BitVec 32
  totNumReports : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  transactTime : BitVec 64
  lastUpdateTime : BitVec 64
  tradeDate : BitVec 16
  mdSecurityTradingStatus : BitVec 8
  highLimitPrice : BitVec 64
  lowLimitPrice : BitVec 64
  maxPriceVariation : BitVec 64
  snapshotFullRefreshGroups : SnapshotFullRefreshGroups
  deriving DecidableEq, Repr

namespace SnapshotFullRefresh

def encode (message : SnapshotFullRefresh) : List UInt8 :=
  encodeUIntLE 4 message.lastMsgSeqNumProcessed
    ++ (encodeUIntLE 4 message.totNumReports
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.lastUpdateTime
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUInt 1 message.mdSecurityTradingStatus
    ++ (encodeUIntLE 8 message.highLimitPrice
    ++ (encodeUIntLE 8 message.lowLimitPrice
    ++ (encodeUIntLE 8 message.maxPriceVariation
    ++ (SnapshotFullRefreshGroups.encode message.snapshotFullRefreshGroups)))))))))))

def decode (bytes : List UInt8) : Option (SnapshotFullRefresh × List UInt8) := do
  let (lastMsgSeqNumProcessed, bytes) ← decodeUIntLE 4 bytes
  let (totNumReports, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (mdSecurityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPriceVariation, bytes) ← decodeUIntLE 8 bytes
  let (snapshotFullRefreshGroups, bytes) ← SnapshotFullRefreshGroups.decode bytes
  pure ({ lastMsgSeqNumProcessed, totNumReports, securityId, rptSeq, transactTime, lastUpdateTime, tradeDate, mdSecurityTradingStatus, highLimitPrice, lowLimitPrice, maxPriceVariation, snapshotFullRefreshGroups }, bytes)

theorem encode_length_pos (message : SnapshotFullRefresh) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotFullRefresh) : (encode message).length ≤ 5672 := by
  have bound_snapshotFullRefreshGroups := SnapshotFullRefreshGroups.encode_length_le message.snapshotFullRefreshGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : SnapshotFullRefresh) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [SnapshotFullRefreshGroups.decode_encode, some_bind]
  rfl

end SnapshotFullRefresh

/-- Related Sym Group: 32 bytes -/
structure RelatedSymGroup where
  symbol : Alpha 20
  securityId : BitVec 32
  orderQty : BitVec 32
  quoteType : BitVec 8
  side : BitVec 8
  padding2 : Alpha 2
  deriving DecidableEq, Repr

namespace RelatedSymGroup

def encode (message : RelatedSymGroup) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUInt 1 message.quoteType
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.padding2)))))

def decode (bytes : List UInt8) : Option (RelatedSymGroup × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  pure ({ symbol, securityId, orderQty, quoteType, side, padding2 }, bytes)

@[simp] theorem encode_length (message : RelatedSymGroup) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RelatedSymGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RelatedSymGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RelatedSymGroup

/-- Related Sym Groups -/
structure RelatedSymGroups where
  blockLength : BitVec 16
  relatedSymGroup : Bounded 1 RelatedSymGroup
  deriving DecidableEq, Repr

namespace RelatedSymGroups

def encode (message : RelatedSymGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.relatedSymGroup.val.length)
    ++ (encodeMany RelatedSymGroup.encode message.relatedSymGroup.val))

def decode (bytes : List UInt8) : Option (RelatedSymGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (relatedSymGroup_, bytes) ← decodeMany RelatedSymGroup.decode numInGroup.toNat bytes
  if fits_relatedSymGroup : relatedSymGroup_.length < 256 ^ 1 then
    pure ({ blockLength, relatedSymGroup := ⟨relatedSymGroup_, fits_relatedSymGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : RelatedSymGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RelatedSymGroups) : (encode message).length ≤ 8163 := by
  have bound_relatedSymGroup := message.relatedSymGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const RelatedSymGroup.encode 32 RelatedSymGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : RelatedSymGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 RelatedSymGroup.encode RelatedSymGroup.decode RelatedSymGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.relatedSymGroup.length_lt]
  rfl

end RelatedSymGroups

/-- Quote Request -/
structure QuoteRequest where
  transactTime : BitVec 64
  quoteReqId : Alpha 23
  matchEventIndicator : BitVec 8
  padding3 : Alpha 3
  relatedSymGroups : RelatedSymGroups
  deriving DecidableEq, Repr

namespace QuoteRequest

def encode (message : QuoteRequest) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (Alpha.encode message.quoteReqId
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.padding3
    ++ (RelatedSymGroups.encode message.relatedSymGroups))))

def decode (bytes : List UInt8) : Option (QuoteRequest × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteReqId, bytes) ← Alpha.decode 23 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding3, bytes) ← Alpha.decode 3 bytes
  let (relatedSymGroups, bytes) ← RelatedSymGroups.decode bytes
  pure ({ transactTime, quoteReqId, matchEventIndicator, padding3, relatedSymGroups }, bytes)

theorem encode_length_pos (message : QuoteRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteRequest) : (encode message).length ≤ 8198 := by
  have bound_relatedSymGroups := RelatedSymGroups.encode_length_le message.relatedSymGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RelatedSymGroups.decode_encode, some_bind]
  rfl

end QuoteRequest

/-- Option Underlyings Group: 24 bytes -/
structure OptionUnderlyingsGroup where
  underlyingSecurityId : BitVec 32
  underlyingSymbol : Alpha 20
  deriving DecidableEq, Repr

namespace OptionUnderlyingsGroup

def encode (message : OptionUnderlyingsGroup) : List UInt8 :=
  encodeUIntLE 4 message.underlyingSecurityId
    ++ (Alpha.encode message.underlyingSymbol)

def decode (bytes : List UInt8) : Option (OptionUnderlyingsGroup × List UInt8) := do
  let (underlyingSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 20 bytes
  pure ({ underlyingSecurityId, underlyingSymbol }, bytes)

@[simp] theorem encode_length (message : OptionUnderlyingsGroup) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OptionUnderlyingsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionUnderlyingsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionUnderlyingsGroup

/-- Option Underlyings Groups -/
structure OptionUnderlyingsGroups where
  blockLength : BitVec 16
  optionUnderlyingsGroup : Bounded 1 OptionUnderlyingsGroup
  deriving DecidableEq, Repr

namespace OptionUnderlyingsGroups

def encode (message : OptionUnderlyingsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.optionUnderlyingsGroup.val.length)
    ++ (encodeMany OptionUnderlyingsGroup.encode message.optionUnderlyingsGroup.val))

def decode (bytes : List UInt8) : Option (OptionUnderlyingsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (optionUnderlyingsGroup_, bytes) ← decodeMany OptionUnderlyingsGroup.decode numInGroup.toNat bytes
  if fits_optionUnderlyingsGroup : optionUnderlyingsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, optionUnderlyingsGroup := ⟨optionUnderlyingsGroup_, fits_optionUnderlyingsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OptionUnderlyingsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OptionUnderlyingsGroups) : (encode message).length ≤ 6123 := by
  have bound_optionUnderlyingsGroup := message.optionUnderlyingsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const OptionUnderlyingsGroup.encode 24 OptionUnderlyingsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OptionUnderlyingsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OptionUnderlyingsGroup.encode OptionUnderlyingsGroup.decode OptionUnderlyingsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.optionUnderlyingsGroup.length_lt]
  rfl

end OptionUnderlyingsGroups

/-- Md Instrument Definition Option -/
structure MdInstrumentDefinitionOption where
  matchEventIndicator : BitVec 8
  totNumReportsOptional : BitVec 32
  securityUpdateAction : SecurityUpdateAction
  lastUpdateTime : BitVec 64
  mdSecurityTradingStatus : BitVec 8
  applId : BitVec 16
  marketSegmentId : BitVec 8
  underlyingProduct : BitVec 8
  securityExchange : Alpha 4
  securityGroup : Alpha 6
  asset : Alpha 6
  symbol : Alpha 20
  securityId : BitVec 32
  securityType : Alpha 6
  cfiCode : Alpha 6
  putOrCall : BitVec 8
  maturityMonthYear : MaturityMonthYear
  currency : Alpha 3
  strikePrice : BitVec 64
  strikeCurrency : Alpha 3
  settlCurrency : Alpha 3
  minCabPrice : BitVec 64
  matchAlgorithm : Alpha 1
  minTradeVol : BitVec 32
  maxTradeVol : BitVec 32
  minPriceIncrementOptional : BitVec 64
  minPriceIncrementAmount : BitVec 64
  displayFactor : BitVec 64
  tickRule : BitVec 8
  mainFraction : BitVec 8
  subFraction : BitVec 8
  priceDisplayFormat : BitVec 8
  unitOfMeasure : Alpha 30
  unitOfMeasureQty : BitVec 64
  tradingReferencePrice : BitVec 64
  settlPriceType : BitVec 8
  clearedVolume : BitVec 32
  openInterestQty : BitVec 32
  lowLimitPrice : BitVec 64
  highLimitPrice : BitVec 64
  userDefinedInstrument : Alpha 1
  eventsGroups : EventsGroups
  feedTypesGroups : FeedTypesGroups
  instAttribGroups : InstAttribGroups
  lotTypeRulesGroups : LotTypeRulesGroups
  optionUnderlyingsGroups : OptionUnderlyingsGroups
  deriving DecidableEq, Repr

namespace MdInstrumentDefinitionOption

def encode (message : MdInstrumentDefinitionOption) : List UInt8 :=
  encodeUIntLE 1 message.matchEventIndicator
    ++ (encodeUIntLE 4 message.totNumReportsOptional
    ++ (SecurityUpdateAction.encode message.securityUpdateAction
    ++ (encodeUIntLE 8 message.lastUpdateTime
    ++ (encodeUInt 1 message.mdSecurityTradingStatus
    ++ (encodeUIntLE 2 message.applId
    ++ (encodeUInt 1 message.marketSegmentId
    ++ (encodeUInt 1 message.underlyingProduct
    ++ (Alpha.encode message.securityExchange
    ++ (Alpha.encode message.securityGroup
    ++ (Alpha.encode message.asset
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.securityId
    ++ (Alpha.encode message.securityType
    ++ (Alpha.encode message.cfiCode
    ++ (encodeUInt 1 message.putOrCall
    ++ (MaturityMonthYear.encode message.maturityMonthYear
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (Alpha.encode message.strikeCurrency
    ++ (Alpha.encode message.settlCurrency
    ++ (encodeUIntLE 8 message.minCabPrice
    ++ (Alpha.encode message.matchAlgorithm
    ++ (encodeUIntLE 4 message.minTradeVol
    ++ (encodeUIntLE 4 message.maxTradeVol
    ++ (encodeUIntLE 8 message.minPriceIncrementOptional
    ++ (encodeUIntLE 8 message.minPriceIncrementAmount
    ++ (encodeUIntLE 8 message.displayFactor
    ++ (encodeUInt 1 message.tickRule
    ++ (encodeUInt 1 message.mainFraction
    ++ (encodeUInt 1 message.subFraction
    ++ (encodeUInt 1 message.priceDisplayFormat
    ++ (Alpha.encode message.unitOfMeasure
    ++ (encodeUIntLE 8 message.unitOfMeasureQty
    ++ (encodeUIntLE 8 message.tradingReferencePrice
    ++ (encodeUIntLE 1 message.settlPriceType
    ++ (encodeUIntLE 4 message.clearedVolume
    ++ (encodeUIntLE 4 message.openInterestQty
    ++ (encodeUIntLE 8 message.lowLimitPrice
    ++ (encodeUIntLE 8 message.highLimitPrice
    ++ (Alpha.encode message.userDefinedInstrument
    ++ (EventsGroups.encode message.eventsGroups
    ++ (FeedTypesGroups.encode message.feedTypesGroups
    ++ (InstAttribGroups.encode message.instAttribGroups
    ++ (LotTypeRulesGroups.encode message.lotTypeRulesGroups
    ++ (OptionUnderlyingsGroups.encode message.optionUnderlyingsGroups)))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MdInstrumentDefinitionOption × List UInt8) := do
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (totNumReportsOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityUpdateAction, bytes) ← SecurityUpdateAction.decode bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (mdSecurityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (applId, bytes) ← decodeUIntLE 2 bytes
  let (marketSegmentId, bytes) ← decodeUInt 1 bytes
  let (underlyingProduct, bytes) ← decodeUInt 1 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  let (asset, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (securityType, bytes) ← Alpha.decode 6 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (strikeCurrency, bytes) ← Alpha.decode 3 bytes
  let (settlCurrency, bytes) ← Alpha.decode 3 bytes
  let (minCabPrice, bytes) ← decodeUIntLE 8 bytes
  let (matchAlgorithm, bytes) ← Alpha.decode 1 bytes
  let (minTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (maxTradeVol, bytes) ← decodeUIntLE 4 bytes
  let (minPriceIncrementOptional, bytes) ← decodeUIntLE 8 bytes
  let (minPriceIncrementAmount, bytes) ← decodeUIntLE 8 bytes
  let (displayFactor, bytes) ← decodeUIntLE 8 bytes
  let (tickRule, bytes) ← decodeUInt 1 bytes
  let (mainFraction, bytes) ← decodeUInt 1 bytes
  let (subFraction, bytes) ← decodeUInt 1 bytes
  let (priceDisplayFormat, bytes) ← decodeUInt 1 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 30 bytes
  let (unitOfMeasureQty, bytes) ← decodeUIntLE 8 bytes
  let (tradingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (clearedVolume, bytes) ← decodeUIntLE 4 bytes
  let (openInterestQty, bytes) ← decodeUIntLE 4 bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (userDefinedInstrument, bytes) ← Alpha.decode 1 bytes
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  let (feedTypesGroups, bytes) ← FeedTypesGroups.decode bytes
  let (instAttribGroups, bytes) ← InstAttribGroups.decode bytes
  let (lotTypeRulesGroups, bytes) ← LotTypeRulesGroups.decode bytes
  let (optionUnderlyingsGroups, bytes) ← OptionUnderlyingsGroups.decode bytes
  pure ({ matchEventIndicator, totNumReportsOptional, securityUpdateAction, lastUpdateTime, mdSecurityTradingStatus, applId, marketSegmentId, underlyingProduct, securityExchange, securityGroup, asset, symbol, securityId, securityType, cfiCode, putOrCall, maturityMonthYear, currency, strikePrice, strikeCurrency, settlCurrency, minCabPrice, matchAlgorithm, minTradeVol, maxTradeVol, minPriceIncrementOptional, minPriceIncrementAmount, displayFactor, tickRule, mainFraction, subFraction, priceDisplayFormat, unitOfMeasure, unitOfMeasureQty, tradingReferencePrice, settlPriceType, clearedVolume, openInterestQty, lowLimitPrice, highLimitPrice, userDefinedInstrument, eventsGroups, feedTypesGroups, instAttribGroups, lotTypeRulesGroups, optionUnderlyingsGroups }, bytes)

theorem encode_length_pos (message : MdInstrumentDefinitionOption) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdInstrumentDefinitionOption) : (encode message).length ≤ 11956 := by
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  have bound_feedTypesGroups := FeedTypesGroups.encode_length_le message.feedTypesGroups
  have bound_instAttribGroups := InstAttribGroups.encode_length_le message.instAttribGroups
  have bound_lotTypeRulesGroups := LotTypeRulesGroups.encode_length_le message.lotTypeRulesGroups
  have bound_optionUnderlyingsGroups := OptionUnderlyingsGroups.encode_length_le message.optionUnderlyingsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SecurityUpdateAction.encode_length, encodeUInt_length, Alpha.encode_length, MaturityMonthYear.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MdInstrumentDefinitionOption) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityUpdateAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MaturityMonthYear.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FeedTypesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstAttribGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LotTypeRulesGroups.decode_encode, some_bind]
  dsimp only
  rw [OptionUnderlyingsGroups.decode_encode, some_bind]
  rfl

end MdInstrumentDefinitionOption

/-- Incremental Refresh Trade Summary Group: 32 bytes -/
structure IncrementalRefreshTradeSummaryGroup where
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 32
  securityId : BitVec 32
  rptSeq : BitVec 32
  numberOfOrders : BitVec 32
  aggressorSide : BitVec 8
  mdUpdateAction : BitVec 8
  padding6 : Alpha 6
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeSummaryGroup

def encode (message : IncrementalRefreshTradeSummaryGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPx
    ++ (encodeUIntLE 4 message.mdEntrySize
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUIntLE 4 message.numberOfOrders
    ++ (encodeUInt 1 message.aggressorSide
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (Alpha.encode message.padding6)))))))

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeSummaryGroup × List UInt8) := do
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (padding6, bytes) ← Alpha.decode 6 bytes
  pure ({ mdEntryPx, mdEntrySize, securityId, rptSeq, numberOfOrders, aggressorSide, mdUpdateAction, padding6 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshTradeSummaryGroup) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IncrementalRefreshTradeSummaryGroup

/-- Incremental Refresh Trade Summary Groups -/
structure IncrementalRefreshTradeSummaryGroups where
  blockLength : BitVec 16
  incrementalRefreshTradeSummaryGroup : Bounded 1 IncrementalRefreshTradeSummaryGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeSummaryGroups

def encode (message : IncrementalRefreshTradeSummaryGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshTradeSummaryGroup.val.length)
    ++ (encodeMany IncrementalRefreshTradeSummaryGroup.encode message.incrementalRefreshTradeSummaryGroup.val))

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeSummaryGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTradeSummaryGroup_, bytes) ← decodeMany IncrementalRefreshTradeSummaryGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshTradeSummaryGroup : incrementalRefreshTradeSummaryGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshTradeSummaryGroup := ⟨incrementalRefreshTradeSummaryGroup_, fits_incrementalRefreshTradeSummaryGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshTradeSummaryGroups) : (encode message).length ≤ 8163 := by
  have bound_incrementalRefreshTradeSummaryGroup := message.incrementalRefreshTradeSummaryGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshTradeSummaryGroup.encode 32 IncrementalRefreshTradeSummaryGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshTradeSummaryGroup.encode IncrementalRefreshTradeSummaryGroup.decode IncrementalRefreshTradeSummaryGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.incrementalRefreshTradeSummaryGroup.length_lt]
  rfl

end IncrementalRefreshTradeSummaryGroups

/-- Incremental Refresh Trade Summary Order Id Group: 16 bytes -/
structure IncrementalRefreshTradeSummaryOrderIdGroup where
  orderId : BitVec 64
  lastQty : BitVec 32
  padding4 : Alpha 4
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeSummaryOrderIdGroup

def encode (message : IncrementalRefreshTradeSummaryOrderIdGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.lastQty
    ++ (Alpha.encode message.padding4))

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeSummaryOrderIdGroup × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (padding4, bytes) ← Alpha.decode 4 bytes
  pure ({ orderId, lastQty, padding4 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshTradeSummaryOrderIdGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryOrderIdGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryOrderIdGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IncrementalRefreshTradeSummaryOrderIdGroup

/-- Incremental Refresh Trade Summary Order Id Groups -/
structure IncrementalRefreshTradeSummaryOrderIdGroups where
  blockLength : BitVec 16
  padding5 : Alpha 5
  incrementalRefreshTradeSummaryOrderIdGroup : Bounded 1 IncrementalRefreshTradeSummaryOrderIdGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshTradeSummaryOrderIdGroups

def encode (message : IncrementalRefreshTradeSummaryOrderIdGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (Alpha.encode message.padding5
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshTradeSummaryOrderIdGroup.val.length)
    ++ (encodeMany IncrementalRefreshTradeSummaryOrderIdGroup.encode message.incrementalRefreshTradeSummaryOrderIdGroup.val)))

def decode (bytes : List UInt8) : Option (IncrementalRefreshTradeSummaryOrderIdGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTradeSummaryOrderIdGroup_, bytes) ← decodeMany IncrementalRefreshTradeSummaryOrderIdGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshTradeSummaryOrderIdGroup : incrementalRefreshTradeSummaryOrderIdGroup_.length < 256 ^ 1 then
    pure ({ blockLength, padding5, incrementalRefreshTradeSummaryOrderIdGroup := ⟨incrementalRefreshTradeSummaryOrderIdGroup_, fits_incrementalRefreshTradeSummaryOrderIdGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshTradeSummaryOrderIdGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshTradeSummaryOrderIdGroups) : (encode message).length ≤ 4088 := by
  have bound_incrementalRefreshTradeSummaryOrderIdGroup := message.incrementalRefreshTradeSummaryOrderIdGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshTradeSummaryOrderIdGroup.encode 16 IncrementalRefreshTradeSummaryOrderIdGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshTradeSummaryOrderIdGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshTradeSummaryOrderIdGroup.encode IncrementalRefreshTradeSummaryOrderIdGroup.decode IncrementalRefreshTradeSummaryOrderIdGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.incrementalRefreshTradeSummaryOrderIdGroup.length_lt]
  rfl

end IncrementalRefreshTradeSummaryOrderIdGroups

/-- Md Incremental Refresh Trade Summary -/
structure MdIncrementalRefreshTradeSummary where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  padding2 : Alpha 2
  incrementalRefreshTradeSummaryGroups : IncrementalRefreshTradeSummaryGroups
  incrementalRefreshTradeSummaryOrderIdGroups : IncrementalRefreshTradeSummaryOrderIdGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshTradeSummary

def encode (message : MdIncrementalRefreshTradeSummary) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.matchEventIndicator
    ++ (Alpha.encode message.padding2
    ++ (IncrementalRefreshTradeSummaryGroups.encode message.incrementalRefreshTradeSummaryGroups
    ++ (IncrementalRefreshTradeSummaryOrderIdGroups.encode message.incrementalRefreshTradeSummaryOrderIdGroups))))

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshTradeSummary × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (padding2, bytes) ← Alpha.decode 2 bytes
  let (incrementalRefreshTradeSummaryGroups, bytes) ← IncrementalRefreshTradeSummaryGroups.decode bytes
  let (incrementalRefreshTradeSummaryOrderIdGroups, bytes) ← IncrementalRefreshTradeSummaryOrderIdGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, padding2, incrementalRefreshTradeSummaryGroups, incrementalRefreshTradeSummaryOrderIdGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshTradeSummary) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshTradeSummary) : (encode message).length ≤ 12262 := by
  have bound_incrementalRefreshTradeSummaryGroups := IncrementalRefreshTradeSummaryGroups.encode_length_le message.incrementalRefreshTradeSummaryGroups
  have bound_incrementalRefreshTradeSummaryOrderIdGroups := IncrementalRefreshTradeSummaryOrderIdGroups.encode_length_le message.incrementalRefreshTradeSummaryOrderIdGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshTradeSummary) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IncrementalRefreshTradeSummaryGroups.decode_encode, some_bind]
  dsimp only
  rw [IncrementalRefreshTradeSummaryOrderIdGroups.decode_encode, some_bind]
  rfl

end MdIncrementalRefreshTradeSummary

/-- Negotiate: 78 bytes -/
structure Negotiate where
  hmacSignature : Alpha 32
  accessKeyId : Alpha 20
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  session : Alpha 5
  firm : Alpha 5
  deriving DecidableEq, Repr

namespace Negotiate

def encode (message : Negotiate) : List UInt8 :=
  Alpha.encode message.hmacSignature
    ++ (Alpha.encode message.accessKeyId
    ++ (encodeUIntLE 8 message.uuid
    ++ (encodeUIntLE 8 message.requestTimestamp
    ++ (Alpha.encode message.session
    ++ (Alpha.encode message.firm)))))

def decode (bytes : List UInt8) : Option (Negotiate × List UInt8) := do
  let (hmacSignature, bytes) ← Alpha.decode 32 bytes
  let (accessKeyId, bytes) ← Alpha.decode 20 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (session, bytes) ← Alpha.decode 5 bytes
  let (firm, bytes) ← Alpha.decode 5 bytes
  pure ({ hmacSignature, accessKeyId, uuid, requestTimestamp, session, firm }, bytes)

@[simp] theorem encode_length (message : Negotiate) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : Negotiate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Negotiate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end Negotiate

/-- Negotiation Reject: 70 bytes -/
structure NegotiationReject where
  reason : Alpha 48
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  errorCodes : BitVec 8
  padding5 : Alpha 5
  deriving DecidableEq, Repr

namespace NegotiationReject

def encode (message : NegotiationReject) : List UInt8 :=
  Alpha.encode message.reason
    ++ (encodeUIntLE 8 message.uuid
    ++ (encodeUIntLE 8 message.requestTimestamp
    ++ (encodeUInt 1 message.errorCodes
    ++ (Alpha.encode message.padding5))))

def decode (bytes : List UInt8) : Option (NegotiationReject × List UInt8) := do
  let (reason, bytes) ← Alpha.decode 48 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (errorCodes, bytes) ← decodeUInt 1 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  pure ({ reason, uuid, requestTimestamp, errorCodes, padding5 }, bytes)

@[simp] theorem encode_length (message : NegotiationReject) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NegotiationReject) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NegotiationReject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NegotiationReject

/-- Negotiation Response: 22 bytes -/
structure NegotiationResponse where
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  secretKeySecureIdExpiration : BitVec 16
  padding4 : Alpha 4
  deriving DecidableEq, Repr

namespace NegotiationResponse

def encode (message : NegotiationResponse) : List UInt8 :=
  encodeUIntLE 8 message.uuid
    ++ (encodeUIntLE 8 message.requestTimestamp
    ++ (encodeUIntLE 2 message.secretKeySecureIdExpiration
    ++ (Alpha.encode message.padding4)))

def decode (bytes : List UInt8) : Option (NegotiationResponse × List UInt8) := do
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (secretKeySecureIdExpiration, bytes) ← decodeUIntLE 2 bytes
  let (padding4, bytes) ← Alpha.decode 4 bytes
  pure ({ uuid, requestTimestamp, secretKeySecureIdExpiration, padding4 }, bytes)

@[simp] theorem encode_length (message : NegotiationResponse) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : NegotiationResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NegotiationResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NegotiationResponse

/-- Terminate: 70 bytes -/
structure Terminate where
  reason : Alpha 48
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  errorCodes : BitVec 8
  padding5 : Alpha 5
  deriving DecidableEq, Repr

namespace Terminate

def encode (message : Terminate) : List UInt8 :=
  Alpha.encode message.reason
    ++ (encodeUIntLE 8 message.uuid
    ++ (encodeUIntLE 8 message.requestTimestamp
    ++ (encodeUInt 1 message.errorCodes
    ++ (Alpha.encode message.padding5))))

def decode (bytes : List UInt8) : Option (Terminate × List UInt8) := do
  let (reason, bytes) ← Alpha.decode 48 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (errorCodes, bytes) ← decodeUInt 1 bytes
  let (padding5, bytes) ← Alpha.decode 5 bytes
  pure ({ reason, uuid, requestTimestamp, errorCodes, padding5 }, bytes)

@[simp] theorem encode_length (message : Terminate) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : Terminate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Terminate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end Terminate

/-- Market Data Request Security Group: 6 bytes -/
structure MarketDataRequestSecurityGroup where
  securityGroup : Alpha 6
  deriving DecidableEq, Repr

namespace MarketDataRequestSecurityGroup

def encode (message : MarketDataRequestSecurityGroup) : List UInt8 :=
  Alpha.encode message.securityGroup

def decode (bytes : List UInt8) : Option (MarketDataRequestSecurityGroup × List UInt8) := do
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  pure ({ securityGroup }, bytes)

@[simp] theorem encode_length (message : MarketDataRequestSecurityGroup) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : MarketDataRequestSecurityGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDataRequestSecurityGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketDataRequestSecurityGroup

/-- Market Data Request Security Groups -/
structure MarketDataRequestSecurityGroups where
  blockLength : BitVec 16
  marketDataRequestSecurityGroup : Bounded 1 MarketDataRequestSecurityGroup
  deriving DecidableEq, Repr

namespace MarketDataRequestSecurityGroups

def encode (message : MarketDataRequestSecurityGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.marketDataRequestSecurityGroup.val.length)
    ++ (encodeMany MarketDataRequestSecurityGroup.encode message.marketDataRequestSecurityGroup.val))

def decode (bytes : List UInt8) : Option (MarketDataRequestSecurityGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (marketDataRequestSecurityGroup_, bytes) ← decodeMany MarketDataRequestSecurityGroup.decode numInGroup.toNat bytes
  if fits_marketDataRequestSecurityGroup : marketDataRequestSecurityGroup_.length < 256 ^ 1 then
    pure ({ blockLength, marketDataRequestSecurityGroup := ⟨marketDataRequestSecurityGroup_, fits_marketDataRequestSecurityGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketDataRequestSecurityGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketDataRequestSecurityGroups) : (encode message).length ≤ 1533 := by
  have bound_marketDataRequestSecurityGroup := message.marketDataRequestSecurityGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const MarketDataRequestSecurityGroup.encode 6 MarketDataRequestSecurityGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketDataRequestSecurityGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 MarketDataRequestSecurityGroup.encode MarketDataRequestSecurityGroup.decode MarketDataRequestSecurityGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDataRequestSecurityGroup.length_lt]
  rfl

end MarketDataRequestSecurityGroups

/-- Market Data Request Related Symbol Group: 4 bytes -/
structure MarketDataRequestRelatedSymbolGroup where
  securityId : BitVec 32
  deriving DecidableEq, Repr

namespace MarketDataRequestRelatedSymbolGroup

def encode (message : MarketDataRequestRelatedSymbolGroup) : List UInt8 :=
  encodeUIntLE 4 message.securityId

def decode (bytes : List UInt8) : Option (MarketDataRequestRelatedSymbolGroup × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId }, bytes)

@[simp] theorem encode_length (message : MarketDataRequestRelatedSymbolGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : MarketDataRequestRelatedSymbolGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDataRequestRelatedSymbolGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketDataRequestRelatedSymbolGroup

/-- Market Data Request Related Symbol Groups -/
structure MarketDataRequestRelatedSymbolGroups where
  blockLength : BitVec 16
  marketDataRequestRelatedSymbolGroup : Bounded 1 MarketDataRequestRelatedSymbolGroup
  deriving DecidableEq, Repr

namespace MarketDataRequestRelatedSymbolGroups

def encode (message : MarketDataRequestRelatedSymbolGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.marketDataRequestRelatedSymbolGroup.val.length)
    ++ (encodeMany MarketDataRequestRelatedSymbolGroup.encode message.marketDataRequestRelatedSymbolGroup.val))

def decode (bytes : List UInt8) : Option (MarketDataRequestRelatedSymbolGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (marketDataRequestRelatedSymbolGroup_, bytes) ← decodeMany MarketDataRequestRelatedSymbolGroup.decode numInGroup.toNat bytes
  if fits_marketDataRequestRelatedSymbolGroup : marketDataRequestRelatedSymbolGroup_.length < 256 ^ 1 then
    pure ({ blockLength, marketDataRequestRelatedSymbolGroup := ⟨marketDataRequestRelatedSymbolGroup_, fits_marketDataRequestRelatedSymbolGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketDataRequestRelatedSymbolGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketDataRequestRelatedSymbolGroups) : (encode message).length ≤ 1023 := by
  have bound_marketDataRequestRelatedSymbolGroup := message.marketDataRequestRelatedSymbolGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const MarketDataRequestRelatedSymbolGroup.encode 4 MarketDataRequestRelatedSymbolGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketDataRequestRelatedSymbolGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 MarketDataRequestRelatedSymbolGroup.encode MarketDataRequestRelatedSymbolGroup.decode MarketDataRequestRelatedSymbolGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDataRequestRelatedSymbolGroup.length_lt]
  rfl

end MarketDataRequestRelatedSymbolGroups

/-- Market Data Request -/
structure MarketDataRequest where
  mdReqId : BitVec 32
  subscriptionReqType : BitVec 8
  marketDataRequestSecurityGroups : MarketDataRequestSecurityGroups
  marketDataRequestRelatedSymbolGroups : MarketDataRequestRelatedSymbolGroups
  deriving DecidableEq, Repr

namespace MarketDataRequest

def encode (message : MarketDataRequest) : List UInt8 :=
  encodeUIntLE 4 message.mdReqId
    ++ (encodeUInt 1 message.subscriptionReqType
    ++ (MarketDataRequestSecurityGroups.encode message.marketDataRequestSecurityGroups
    ++ (MarketDataRequestRelatedSymbolGroups.encode message.marketDataRequestRelatedSymbolGroups)))

def decode (bytes : List UInt8) : Option (MarketDataRequest × List UInt8) := do
  let (mdReqId, bytes) ← decodeUIntLE 4 bytes
  let (subscriptionReqType, bytes) ← decodeUInt 1 bytes
  let (marketDataRequestSecurityGroups, bytes) ← MarketDataRequestSecurityGroups.decode bytes
  let (marketDataRequestRelatedSymbolGroups, bytes) ← MarketDataRequestRelatedSymbolGroups.decode bytes
  pure ({ mdReqId, subscriptionReqType, marketDataRequestSecurityGroups, marketDataRequestRelatedSymbolGroups }, bytes)

theorem encode_length_pos (message : MarketDataRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketDataRequest) : (encode message).length ≤ 2561 := by
  have bound_marketDataRequestSecurityGroups := MarketDataRequestSecurityGroups.encode_length_le message.marketDataRequestSecurityGroups
  have bound_marketDataRequestRelatedSymbolGroups := MarketDataRequestRelatedSymbolGroups.encode_length_le message.marketDataRequestRelatedSymbolGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : MarketDataRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MarketDataRequestSecurityGroups.decode_encode, some_bind]
  dsimp only
  rw [MarketDataRequestRelatedSymbolGroups.decode_encode, some_bind]
  rfl

end MarketDataRequest

/-- Request Ack Security Group: 6 bytes -/
structure RequestAckSecurityGroup where
  securityGroup : Alpha 6
  deriving DecidableEq, Repr

namespace RequestAckSecurityGroup

def encode (message : RequestAckSecurityGroup) : List UInt8 :=
  Alpha.encode message.securityGroup

def decode (bytes : List UInt8) : Option (RequestAckSecurityGroup × List UInt8) := do
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  pure ({ securityGroup }, bytes)

@[simp] theorem encode_length (message : RequestAckSecurityGroup) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : RequestAckSecurityGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestAckSecurityGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end RequestAckSecurityGroup

/-- Request Ack Security Groups -/
structure RequestAckSecurityGroups where
  blockLength : BitVec 16
  requestAckSecurityGroup : Bounded 1 RequestAckSecurityGroup
  deriving DecidableEq, Repr

namespace RequestAckSecurityGroups

def encode (message : RequestAckSecurityGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.requestAckSecurityGroup.val.length)
    ++ (encodeMany RequestAckSecurityGroup.encode message.requestAckSecurityGroup.val))

def decode (bytes : List UInt8) : Option (RequestAckSecurityGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (requestAckSecurityGroup_, bytes) ← decodeMany RequestAckSecurityGroup.decode numInGroup.toNat bytes
  if fits_requestAckSecurityGroup : requestAckSecurityGroup_.length < 256 ^ 1 then
    pure ({ blockLength, requestAckSecurityGroup := ⟨requestAckSecurityGroup_, fits_requestAckSecurityGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : RequestAckSecurityGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RequestAckSecurityGroups) : (encode message).length ≤ 1533 := by
  have bound_requestAckSecurityGroup := message.requestAckSecurityGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const RequestAckSecurityGroup.encode 6 RequestAckSecurityGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : RequestAckSecurityGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 RequestAckSecurityGroup.encode RequestAckSecurityGroup.decode RequestAckSecurityGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.requestAckSecurityGroup.length_lt]
  rfl

end RequestAckSecurityGroups

/-- Request Ack Related Symbol Group: 4 bytes -/
structure RequestAckRelatedSymbolGroup where
  securityId : BitVec 32
  deriving DecidableEq, Repr

namespace RequestAckRelatedSymbolGroup

def encode (message : RequestAckRelatedSymbolGroup) : List UInt8 :=
  encodeUIntLE 4 message.securityId

def decode (bytes : List UInt8) : Option (RequestAckRelatedSymbolGroup × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId }, bytes)

@[simp] theorem encode_length (message : RequestAckRelatedSymbolGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : RequestAckRelatedSymbolGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestAckRelatedSymbolGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RequestAckRelatedSymbolGroup

/-- Request Ack Related Symbol Groups -/
structure RequestAckRelatedSymbolGroups where
  blockLength : BitVec 16
  requestAckRelatedSymbolGroup : Bounded 1 RequestAckRelatedSymbolGroup
  deriving DecidableEq, Repr

namespace RequestAckRelatedSymbolGroups

def encode (message : RequestAckRelatedSymbolGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.requestAckRelatedSymbolGroup.val.length)
    ++ (encodeMany RequestAckRelatedSymbolGroup.encode message.requestAckRelatedSymbolGroup.val))

def decode (bytes : List UInt8) : Option (RequestAckRelatedSymbolGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (requestAckRelatedSymbolGroup_, bytes) ← decodeMany RequestAckRelatedSymbolGroup.decode numInGroup.toNat bytes
  if fits_requestAckRelatedSymbolGroup : requestAckRelatedSymbolGroup_.length < 256 ^ 1 then
    pure ({ blockLength, requestAckRelatedSymbolGroup := ⟨requestAckRelatedSymbolGroup_, fits_requestAckRelatedSymbolGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : RequestAckRelatedSymbolGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RequestAckRelatedSymbolGroups) : (encode message).length ≤ 1023 := by
  have bound_requestAckRelatedSymbolGroup := message.requestAckRelatedSymbolGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const RequestAckRelatedSymbolGroup.encode 4 RequestAckRelatedSymbolGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : RequestAckRelatedSymbolGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 RequestAckRelatedSymbolGroup.encode RequestAckRelatedSymbolGroup.decode RequestAckRelatedSymbolGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.requestAckRelatedSymbolGroup.length_lt]
  rfl

end RequestAckRelatedSymbolGroups

/-- Request Ack -/
structure RequestAck where
  mdReqId : BitVec 32
  subscriptionReqType : BitVec 8
  mdReqIdStatus : BitVec 8
  requestAckSecurityGroups : RequestAckSecurityGroups
  requestAckRelatedSymbolGroups : RequestAckRelatedSymbolGroups
  deriving DecidableEq, Repr

namespace RequestAck

def encode (message : RequestAck) : List UInt8 :=
  encodeUIntLE 4 message.mdReqId
    ++ (encodeUInt 1 message.subscriptionReqType
    ++ (encodeUInt 1 message.mdReqIdStatus
    ++ (RequestAckSecurityGroups.encode message.requestAckSecurityGroups
    ++ (RequestAckRelatedSymbolGroups.encode message.requestAckRelatedSymbolGroups))))

def decode (bytes : List UInt8) : Option (RequestAck × List UInt8) := do
  let (mdReqId, bytes) ← decodeUIntLE 4 bytes
  let (subscriptionReqType, bytes) ← decodeUInt 1 bytes
  let (mdReqIdStatus, bytes) ← decodeUInt 1 bytes
  let (requestAckSecurityGroups, bytes) ← RequestAckSecurityGroups.decode bytes
  let (requestAckRelatedSymbolGroups, bytes) ← RequestAckRelatedSymbolGroups.decode bytes
  pure ({ mdReqId, subscriptionReqType, mdReqIdStatus, requestAckSecurityGroups, requestAckRelatedSymbolGroups }, bytes)

theorem encode_length_pos (message : RequestAck) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RequestAck) : (encode message).length ≤ 2562 := by
  have bound_requestAckSecurityGroups := RequestAckSecurityGroups.encode_length_le message.requestAckSecurityGroups
  have bound_requestAckRelatedSymbolGroups := RequestAckRelatedSymbolGroups.encode_length_le message.requestAckRelatedSymbolGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : RequestAck) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RequestAckSecurityGroups.decode_encode, some_bind]
  dsimp only
  rw [RequestAckRelatedSymbolGroups.decode_encode, some_bind]
  rfl

end RequestAck

/-- Request Reject: 105 bytes -/
structure RequestReject where
  mdReqIdOptional : BitVec 32
  mdReqRejReason : BitVec 8
  text : Alpha 100
  deriving DecidableEq, Repr

namespace RequestReject

def encode (message : RequestReject) : List UInt8 :=
  encodeUIntLE 4 message.mdReqIdOptional
    ++ (encodeUInt 1 message.mdReqRejReason
    ++ (Alpha.encode message.text))

def decode (bytes : List UInt8) : Option (RequestReject × List UInt8) := do
  let (mdReqIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (mdReqRejReason, bytes) ← decodeUInt 1 bytes
  let (text, bytes) ← Alpha.decode 100 bytes
  pure ({ mdReqIdOptional, mdReqRejReason, text }, bytes)

@[simp] theorem encode_length (message : RequestReject) : (encode message).length = 105 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RequestReject) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestReject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RequestReject

/-- Security List Request Security Group: 6 bytes -/
structure SecurityListRequestSecurityGroup where
  securityGroup : Alpha 6
  deriving DecidableEq, Repr

namespace SecurityListRequestSecurityGroup

def encode (message : SecurityListRequestSecurityGroup) : List UInt8 :=
  Alpha.encode message.securityGroup

def decode (bytes : List UInt8) : Option (SecurityListRequestSecurityGroup × List UInt8) := do
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  pure ({ securityGroup }, bytes)

@[simp] theorem encode_length (message : SecurityListRequestSecurityGroup) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SecurityListRequestSecurityGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityListRequestSecurityGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityListRequestSecurityGroup

/-- Security List Request Security Groups -/
structure SecurityListRequestSecurityGroups where
  blockLength : BitVec 16
  securityListRequestSecurityGroup : Bounded 1 SecurityListRequestSecurityGroup
  deriving DecidableEq, Repr

namespace SecurityListRequestSecurityGroups

def encode (message : SecurityListRequestSecurityGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityListRequestSecurityGroup.val.length)
    ++ (encodeMany SecurityListRequestSecurityGroup.encode message.securityListRequestSecurityGroup.val))

def decode (bytes : List UInt8) : Option (SecurityListRequestSecurityGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityListRequestSecurityGroup_, bytes) ← decodeMany SecurityListRequestSecurityGroup.decode numInGroup.toNat bytes
  if fits_securityListRequestSecurityGroup : securityListRequestSecurityGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityListRequestSecurityGroup := ⟨securityListRequestSecurityGroup_, fits_securityListRequestSecurityGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityListRequestSecurityGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityListRequestSecurityGroups) : (encode message).length ≤ 1533 := by
  have bound_securityListRequestSecurityGroup := message.securityListRequestSecurityGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityListRequestSecurityGroup.encode 6 SecurityListRequestSecurityGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityListRequestSecurityGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityListRequestSecurityGroup.encode SecurityListRequestSecurityGroup.decode SecurityListRequestSecurityGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityListRequestSecurityGroup.length_lt]
  rfl

end SecurityListRequestSecurityGroups

/-- Security List Request Related Symbol Group: 4 bytes -/
structure SecurityListRequestRelatedSymbolGroup where
  securityId : BitVec 32
  deriving DecidableEq, Repr

namespace SecurityListRequestRelatedSymbolGroup

def encode (message : SecurityListRequestRelatedSymbolGroup) : List UInt8 :=
  encodeUIntLE 4 message.securityId

def decode (bytes : List UInt8) : Option (SecurityListRequestRelatedSymbolGroup × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId }, bytes)

@[simp] theorem encode_length (message : SecurityListRequestRelatedSymbolGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SecurityListRequestRelatedSymbolGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityListRequestRelatedSymbolGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityListRequestRelatedSymbolGroup

/-- Security List Request Related Symbol Groups -/
structure SecurityListRequestRelatedSymbolGroups where
  blockLength : BitVec 16
  securityListRequestRelatedSymbolGroup : Bounded 1 SecurityListRequestRelatedSymbolGroup
  deriving DecidableEq, Repr

namespace SecurityListRequestRelatedSymbolGroups

def encode (message : SecurityListRequestRelatedSymbolGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityListRequestRelatedSymbolGroup.val.length)
    ++ (encodeMany SecurityListRequestRelatedSymbolGroup.encode message.securityListRequestRelatedSymbolGroup.val))

def decode (bytes : List UInt8) : Option (SecurityListRequestRelatedSymbolGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityListRequestRelatedSymbolGroup_, bytes) ← decodeMany SecurityListRequestRelatedSymbolGroup.decode numInGroup.toNat bytes
  if fits_securityListRequestRelatedSymbolGroup : securityListRequestRelatedSymbolGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityListRequestRelatedSymbolGroup := ⟨securityListRequestRelatedSymbolGroup_, fits_securityListRequestRelatedSymbolGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityListRequestRelatedSymbolGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityListRequestRelatedSymbolGroups) : (encode message).length ≤ 1023 := by
  have bound_securityListRequestRelatedSymbolGroup := message.securityListRequestRelatedSymbolGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityListRequestRelatedSymbolGroup.encode 4 SecurityListRequestRelatedSymbolGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityListRequestRelatedSymbolGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityListRequestRelatedSymbolGroup.encode SecurityListRequestRelatedSymbolGroup.decode SecurityListRequestRelatedSymbolGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityListRequestRelatedSymbolGroup.length_lt]
  rfl

end SecurityListRequestRelatedSymbolGroups

/-- Security List Request -/
structure SecurityListRequest where
  mdReqId : BitVec 32
  subscriptionReqType : BitVec 8
  securityListRequestSecurityGroups : SecurityListRequestSecurityGroups
  securityListRequestRelatedSymbolGroups : SecurityListRequestRelatedSymbolGroups
  deriving DecidableEq, Repr

namespace SecurityListRequest

def encode (message : SecurityListRequest) : List UInt8 :=
  encodeUIntLE 4 message.mdReqId
    ++ (encodeUInt 1 message.subscriptionReqType
    ++ (SecurityListRequestSecurityGroups.encode message.securityListRequestSecurityGroups
    ++ (SecurityListRequestRelatedSymbolGroups.encode message.securityListRequestRelatedSymbolGroups)))

def decode (bytes : List UInt8) : Option (SecurityListRequest × List UInt8) := do
  let (mdReqId, bytes) ← decodeUIntLE 4 bytes
  let (subscriptionReqType, bytes) ← decodeUInt 1 bytes
  let (securityListRequestSecurityGroups, bytes) ← SecurityListRequestSecurityGroups.decode bytes
  let (securityListRequestRelatedSymbolGroups, bytes) ← SecurityListRequestRelatedSymbolGroups.decode bytes
  pure ({ mdReqId, subscriptionReqType, securityListRequestSecurityGroups, securityListRequestRelatedSymbolGroups }, bytes)

theorem encode_length_pos (message : SecurityListRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityListRequest) : (encode message).length ≤ 2561 := by
  have bound_securityListRequestSecurityGroups := SecurityListRequestSecurityGroups.encode_length_le message.securityListRequestSecurityGroups
  have bound_securityListRequestRelatedSymbolGroups := SecurityListRequestRelatedSymbolGroups.encode_length_le message.securityListRequestRelatedSymbolGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : SecurityListRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityListRequestSecurityGroups.decode_encode, some_bind]
  dsimp only
  rw [SecurityListRequestRelatedSymbolGroups.decode_encode, some_bind]
  rfl

end SecurityListRequest

/-- Security Status Request Security Group: 6 bytes -/
structure SecurityStatusRequestSecurityGroup where
  securityGroup : Alpha 6
  deriving DecidableEq, Repr

namespace SecurityStatusRequestSecurityGroup

def encode (message : SecurityStatusRequestSecurityGroup) : List UInt8 :=
  Alpha.encode message.securityGroup

def decode (bytes : List UInt8) : Option (SecurityStatusRequestSecurityGroup × List UInt8) := do
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  pure ({ securityGroup }, bytes)

@[simp] theorem encode_length (message : SecurityStatusRequestSecurityGroup) : (encode message).length = 6 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SecurityStatusRequestSecurityGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusRequestSecurityGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityStatusRequestSecurityGroup

/-- Security Status Request Security Groups -/
structure SecurityStatusRequestSecurityGroups where
  blockLength : BitVec 16
  securityStatusRequestSecurityGroup : Bounded 1 SecurityStatusRequestSecurityGroup
  deriving DecidableEq, Repr

namespace SecurityStatusRequestSecurityGroups

def encode (message : SecurityStatusRequestSecurityGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityStatusRequestSecurityGroup.val.length)
    ++ (encodeMany SecurityStatusRequestSecurityGroup.encode message.securityStatusRequestSecurityGroup.val))

def decode (bytes : List UInt8) : Option (SecurityStatusRequestSecurityGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityStatusRequestSecurityGroup_, bytes) ← decodeMany SecurityStatusRequestSecurityGroup.decode numInGroup.toNat bytes
  if fits_securityStatusRequestSecurityGroup : securityStatusRequestSecurityGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityStatusRequestSecurityGroup := ⟨securityStatusRequestSecurityGroup_, fits_securityStatusRequestSecurityGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityStatusRequestSecurityGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityStatusRequestSecurityGroups) : (encode message).length ≤ 1533 := by
  have bound_securityStatusRequestSecurityGroup := message.securityStatusRequestSecurityGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityStatusRequestSecurityGroup.encode 6 SecurityStatusRequestSecurityGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityStatusRequestSecurityGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityStatusRequestSecurityGroup.encode SecurityStatusRequestSecurityGroup.decode SecurityStatusRequestSecurityGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityStatusRequestSecurityGroup.length_lt]
  rfl

end SecurityStatusRequestSecurityGroups

/-- Security Status Request Related Symbol Group: 4 bytes -/
structure SecurityStatusRequestRelatedSymbolGroup where
  securityId : BitVec 32
  deriving DecidableEq, Repr

namespace SecurityStatusRequestRelatedSymbolGroup

def encode (message : SecurityStatusRequestRelatedSymbolGroup) : List UInt8 :=
  encodeUIntLE 4 message.securityId

def decode (bytes : List UInt8) : Option (SecurityStatusRequestRelatedSymbolGroup × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId }, bytes)

@[simp] theorem encode_length (message : SecurityStatusRequestRelatedSymbolGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SecurityStatusRequestRelatedSymbolGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusRequestRelatedSymbolGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityStatusRequestRelatedSymbolGroup

/-- Security Status Request Related Symbol Groups -/
structure SecurityStatusRequestRelatedSymbolGroups where
  blockLength : BitVec 16
  securityStatusRequestRelatedSymbolGroup : Bounded 1 SecurityStatusRequestRelatedSymbolGroup
  deriving DecidableEq, Repr

namespace SecurityStatusRequestRelatedSymbolGroups

def encode (message : SecurityStatusRequestRelatedSymbolGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityStatusRequestRelatedSymbolGroup.val.length)
    ++ (encodeMany SecurityStatusRequestRelatedSymbolGroup.encode message.securityStatusRequestRelatedSymbolGroup.val))

def decode (bytes : List UInt8) : Option (SecurityStatusRequestRelatedSymbolGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (securityStatusRequestRelatedSymbolGroup_, bytes) ← decodeMany SecurityStatusRequestRelatedSymbolGroup.decode numInGroup.toNat bytes
  if fits_securityStatusRequestRelatedSymbolGroup : securityStatusRequestRelatedSymbolGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityStatusRequestRelatedSymbolGroup := ⟨securityStatusRequestRelatedSymbolGroup_, fits_securityStatusRequestRelatedSymbolGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityStatusRequestRelatedSymbolGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityStatusRequestRelatedSymbolGroups) : (encode message).length ≤ 1023 := by
  have bound_securityStatusRequestRelatedSymbolGroup := message.securityStatusRequestRelatedSymbolGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityStatusRequestRelatedSymbolGroup.encode 4 SecurityStatusRequestRelatedSymbolGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityStatusRequestRelatedSymbolGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityStatusRequestRelatedSymbolGroup.encode SecurityStatusRequestRelatedSymbolGroup.decode SecurityStatusRequestRelatedSymbolGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityStatusRequestRelatedSymbolGroup.length_lt]
  rfl

end SecurityStatusRequestRelatedSymbolGroups

/-- Security Status Request -/
structure SecurityStatusRequest where
  mdReqId : BitVec 32
  subscriptionReqType : BitVec 8
  securityStatusRequestSecurityGroups : SecurityStatusRequestSecurityGroups
  securityStatusRequestRelatedSymbolGroups : SecurityStatusRequestRelatedSymbolGroups
  deriving DecidableEq, Repr

namespace SecurityStatusRequest

def encode (message : SecurityStatusRequest) : List UInt8 :=
  encodeUIntLE 4 message.mdReqId
    ++ (encodeUInt 1 message.subscriptionReqType
    ++ (SecurityStatusRequestSecurityGroups.encode message.securityStatusRequestSecurityGroups
    ++ (SecurityStatusRequestRelatedSymbolGroups.encode message.securityStatusRequestRelatedSymbolGroups)))

def decode (bytes : List UInt8) : Option (SecurityStatusRequest × List UInt8) := do
  let (mdReqId, bytes) ← decodeUIntLE 4 bytes
  let (subscriptionReqType, bytes) ← decodeUInt 1 bytes
  let (securityStatusRequestSecurityGroups, bytes) ← SecurityStatusRequestSecurityGroups.decode bytes
  let (securityStatusRequestRelatedSymbolGroups, bytes) ← SecurityStatusRequestRelatedSymbolGroups.decode bytes
  pure ({ mdReqId, subscriptionReqType, securityStatusRequestSecurityGroups, securityStatusRequestRelatedSymbolGroups }, bytes)

theorem encode_length_pos (message : SecurityStatusRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityStatusRequest) : (encode message).length ≤ 2561 := by
  have bound_securityStatusRequestSecurityGroups := SecurityStatusRequestSecurityGroups.encode_length_le message.securityStatusRequestSecurityGroups
  have bound_securityStatusRequestRelatedSymbolGroups := SecurityStatusRequestRelatedSymbolGroups.encode_length_le message.securityStatusRequestRelatedSymbolGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : SecurityStatusRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityStatusRequestSecurityGroups.decode_encode, some_bind]
  dsimp only
  rw [SecurityStatusRequestRelatedSymbolGroups.decode_encode, some_bind]
  rfl

end SecurityStatusRequest

/-- Subscriber Heartbeat: 0 bytes -/
structure SubscriberHeartbeat where
  deriving DecidableEq, Repr

namespace SubscriberHeartbeat

def encode (_ : SubscriberHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SubscriberHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SubscriberHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SubscriberHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end SubscriberHeartbeat

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | channelReset (message : ChannelReset) -- 4
  | adminHeartbeat (message : AdminHeartbeat) -- 12
  | adminLogin (message : AdminLogin) -- 15
  | adminLogout (message : AdminLogout) -- 16
  | mdInstrumentDefinitionFuture (message : MdInstrumentDefinitionFuture) -- 27
  | mdInstrumentDefinitionSpread (message : MdInstrumentDefinitionSpread) -- 29
  | securityStatus (message : SecurityStatus) -- 30
  | mdIncrementalRefreshBook (message : MdIncrementalRefreshBook) -- 32
  | mdIncrementalRefreshDailyStatistics (message : MdIncrementalRefreshDailyStatistics) -- 33
  | mdIncrementalRefreshLimitsBanding (message : MdIncrementalRefreshLimitsBanding) -- 34
  | mdIncrementalRefreshSessionStatistics (message : MdIncrementalRefreshSessionStatistics) -- 35
  | mdIncrementalRefreshTrade (message : MdIncrementalRefreshTrade) -- 36
  | mdIncrementalRefreshVolume (message : MdIncrementalRefreshVolume) -- 37
  | snapshotFullRefresh (message : SnapshotFullRefresh) -- 38
  | quoteRequest (message : QuoteRequest) -- 39
  | mdInstrumentDefinitionOption (message : MdInstrumentDefinitionOption) -- 41
  | mdIncrementalRefreshTradeSummary (message : MdIncrementalRefreshTradeSummary) -- 42
  | negotiate (message : Negotiate) -- 200
  | negotiationReject (message : NegotiationReject) -- 201
  | negotiationResponse (message : NegotiationResponse) -- 202
  | terminate (message : Terminate) -- 203
  | marketDataRequest (message : MarketDataRequest) -- 205
  | requestAck (message : RequestAck) -- 206
  | requestReject (message : RequestReject) -- 207
  | securityListRequest (message : SecurityListRequest) -- 208
  | securityStatusRequest (message : SecurityStatusRequest) -- 209
  | subscriberHeartbeat (message : SubscriberHeartbeat) -- 210
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .channelReset _ => 4
  | .adminHeartbeat _ => 12
  | .adminLogin _ => 15
  | .adminLogout _ => 16
  | .mdInstrumentDefinitionFuture _ => 27
  | .mdInstrumentDefinitionSpread _ => 29
  | .securityStatus _ => 30
  | .mdIncrementalRefreshBook _ => 32
  | .mdIncrementalRefreshDailyStatistics _ => 33
  | .mdIncrementalRefreshLimitsBanding _ => 34
  | .mdIncrementalRefreshSessionStatistics _ => 35
  | .mdIncrementalRefreshTrade _ => 36
  | .mdIncrementalRefreshVolume _ => 37
  | .snapshotFullRefresh _ => 38
  | .quoteRequest _ => 39
  | .mdInstrumentDefinitionOption _ => 41
  | .mdIncrementalRefreshTradeSummary _ => 42
  | .negotiate _ => 200
  | .negotiationReject _ => 201
  | .negotiationResponse _ => 202
  | .terminate _ => 203
  | .marketDataRequest _ => 205
  | .requestAck _ => 206
  | .requestReject _ => 207
  | .securityListRequest _ => 208
  | .securityStatusRequest _ => 209
  | .subscriberHeartbeat _ => 210

def encode : Payload → List UInt8
  | .channelReset message => ChannelReset.encode message
  | .adminHeartbeat message => AdminHeartbeat.encode message
  | .adminLogin message => AdminLogin.encode message
  | .adminLogout message => AdminLogout.encode message
  | .mdInstrumentDefinitionFuture message => MdInstrumentDefinitionFuture.encode message
  | .mdInstrumentDefinitionSpread message => MdInstrumentDefinitionSpread.encode message
  | .securityStatus message => SecurityStatus.encode message
  | .mdIncrementalRefreshBook message => MdIncrementalRefreshBook.encode message
  | .mdIncrementalRefreshDailyStatistics message => MdIncrementalRefreshDailyStatistics.encode message
  | .mdIncrementalRefreshLimitsBanding message => MdIncrementalRefreshLimitsBanding.encode message
  | .mdIncrementalRefreshSessionStatistics message => MdIncrementalRefreshSessionStatistics.encode message
  | .mdIncrementalRefreshTrade message => MdIncrementalRefreshTrade.encode message
  | .mdIncrementalRefreshVolume message => MdIncrementalRefreshVolume.encode message
  | .snapshotFullRefresh message => SnapshotFullRefresh.encode message
  | .quoteRequest message => QuoteRequest.encode message
  | .mdInstrumentDefinitionOption message => MdInstrumentDefinitionOption.encode message
  | .mdIncrementalRefreshTradeSummary message => MdIncrementalRefreshTradeSummary.encode message
  | .negotiate message => Negotiate.encode message
  | .negotiationReject message => NegotiationReject.encode message
  | .negotiationResponse message => NegotiationResponse.encode message
  | .terminate message => Terminate.encode message
  | .marketDataRequest message => MarketDataRequest.encode message
  | .requestAck message => RequestAck.encode message
  | .requestReject message => RequestReject.encode message
  | .securityListRequest message => SecurityListRequest.encode message
  | .securityStatusRequest message => SecurityStatusRequest.encode message
  | .subscriberHeartbeat message => SubscriberHeartbeat.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 12262 := by
  cases message with
  | channelReset inner =>
    have bound_inner := ChannelReset.encode_length_le inner
    simp only [encode]
    omega
  | adminHeartbeat inner =>
    simp only [encode, AdminHeartbeat.encode_length]
    omega
  | adminLogin inner =>
    simp only [encode, AdminLogin.encode_length]
    omega
  | adminLogout inner =>
    simp only [encode, AdminLogout.encode_length]
    omega
  | mdInstrumentDefinitionFuture inner =>
    have bound_inner := MdInstrumentDefinitionFuture.encode_length_le inner
    simp only [encode]
    omega
  | mdInstrumentDefinitionSpread inner =>
    have bound_inner := MdInstrumentDefinitionSpread.encode_length_le inner
    simp only [encode]
    omega
  | securityStatus inner =>
    simp only [encode, SecurityStatus.encode_length]
    omega
  | mdIncrementalRefreshBook inner =>
    have bound_inner := MdIncrementalRefreshBook.encode_length_le inner
    simp only [encode]
    omega
  | mdIncrementalRefreshDailyStatistics inner =>
    have bound_inner := MdIncrementalRefreshDailyStatistics.encode_length_le inner
    simp only [encode]
    omega
  | mdIncrementalRefreshLimitsBanding inner =>
    have bound_inner := MdIncrementalRefreshLimitsBanding.encode_length_le inner
    simp only [encode]
    omega
  | mdIncrementalRefreshSessionStatistics inner =>
    have bound_inner := MdIncrementalRefreshSessionStatistics.encode_length_le inner
    simp only [encode]
    omega
  | mdIncrementalRefreshTrade inner =>
    have bound_inner := MdIncrementalRefreshTrade.encode_length_le inner
    simp only [encode]
    omega
  | mdIncrementalRefreshVolume inner =>
    have bound_inner := MdIncrementalRefreshVolume.encode_length_le inner
    simp only [encode]
    omega
  | snapshotFullRefresh inner =>
    have bound_inner := SnapshotFullRefresh.encode_length_le inner
    simp only [encode]
    omega
  | quoteRequest inner =>
    have bound_inner := QuoteRequest.encode_length_le inner
    simp only [encode]
    omega
  | mdInstrumentDefinitionOption inner =>
    have bound_inner := MdInstrumentDefinitionOption.encode_length_le inner
    simp only [encode]
    omega
  | mdIncrementalRefreshTradeSummary inner =>
    have bound_inner := MdIncrementalRefreshTradeSummary.encode_length_le inner
    simp only [encode]
    omega
  | negotiate inner =>
    simp only [encode, Negotiate.encode_length]
    omega
  | negotiationReject inner =>
    simp only [encode, NegotiationReject.encode_length]
    omega
  | negotiationResponse inner =>
    simp only [encode, NegotiationResponse.encode_length]
    omega
  | terminate inner =>
    simp only [encode, Terminate.encode_length]
    omega
  | marketDataRequest inner =>
    have bound_inner := MarketDataRequest.encode_length_le inner
    simp only [encode]
    omega
  | requestAck inner =>
    have bound_inner := RequestAck.encode_length_le inner
    simp only [encode]
    omega
  | requestReject inner =>
    simp only [encode, RequestReject.encode_length]
    omega
  | securityListRequest inner =>
    have bound_inner := SecurityListRequest.encode_length_le inner
    simp only [encode]
    omega
  | securityStatusRequest inner =>
    have bound_inner := SecurityStatusRequest.encode_length_le inner
    simp only [encode]
    omega
  | subscriberHeartbeat inner =>
    simp only [encode, SubscriberHeartbeat.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 4 then (ChannelReset.decode bytes).map fun (message, rest) => (.channelReset message, rest)
  else if tag = 12 then (AdminHeartbeat.decode bytes).map fun (message, rest) => (.adminHeartbeat message, rest)
  else if tag = 15 then (AdminLogin.decode bytes).map fun (message, rest) => (.adminLogin message, rest)
  else if tag = 16 then (AdminLogout.decode bytes).map fun (message, rest) => (.adminLogout message, rest)
  else if tag = 27 then (MdInstrumentDefinitionFuture.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionFuture message, rest)
  else if tag = 29 then (MdInstrumentDefinitionSpread.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionSpread message, rest)
  else if tag = 30 then (SecurityStatus.decode bytes).map fun (message, rest) => (.securityStatus message, rest)
  else if tag = 32 then (MdIncrementalRefreshBook.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshBook message, rest)
  else if tag = 33 then (MdIncrementalRefreshDailyStatistics.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshDailyStatistics message, rest)
  else if tag = 34 then (MdIncrementalRefreshLimitsBanding.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshLimitsBanding message, rest)
  else if tag = 35 then (MdIncrementalRefreshSessionStatistics.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshSessionStatistics message, rest)
  else if tag = 36 then (MdIncrementalRefreshTrade.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshTrade message, rest)
  else if tag = 37 then (MdIncrementalRefreshVolume.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshVolume message, rest)
  else if tag = 38 then (SnapshotFullRefresh.decode bytes).map fun (message, rest) => (.snapshotFullRefresh message, rest)
  else if tag = 39 then (QuoteRequest.decode bytes).map fun (message, rest) => (.quoteRequest message, rest)
  else if tag = 41 then (MdInstrumentDefinitionOption.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionOption message, rest)
  else if tag = 42 then (MdIncrementalRefreshTradeSummary.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshTradeSummary message, rest)
  else if tag = 200 then (Negotiate.decode bytes).map fun (message, rest) => (.negotiate message, rest)
  else if tag = 201 then (NegotiationReject.decode bytes).map fun (message, rest) => (.negotiationReject message, rest)
  else if tag = 202 then (NegotiationResponse.decode bytes).map fun (message, rest) => (.negotiationResponse message, rest)
  else if tag = 203 then (Terminate.decode bytes).map fun (message, rest) => (.terminate message, rest)
  else if tag = 205 then (MarketDataRequest.decode bytes).map fun (message, rest) => (.marketDataRequest message, rest)
  else if tag = 206 then (RequestAck.decode bytes).map fun (message, rest) => (.requestAck message, rest)
  else if tag = 207 then (RequestReject.decode bytes).map fun (message, rest) => (.requestReject message, rest)
  else if tag = 208 then (SecurityListRequest.decode bytes).map fun (message, rest) => (.securityListRequest message, rest)
  else if tag = 209 then (SecurityStatusRequest.decode bytes).map fun (message, rest) => (.securityStatusRequest message, rest)
  else if tag = 210 then (SubscriberHeartbeat.decode bytes).map fun (message, rest) => (.subscriberHeartbeat message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload))))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | channelReset inner =>
    have bound_inner := ChannelReset.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | adminHeartbeat inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AdminHeartbeat.encode_length]
    omega
  | adminLogin inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AdminLogin.encode_length]
    omega
  | adminLogout inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AdminLogout.encode_length]
    omega
  | mdInstrumentDefinitionFuture inner =>
    have bound_inner := MdInstrumentDefinitionFuture.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | mdInstrumentDefinitionSpread inner =>
    have bound_inner := MdInstrumentDefinitionSpread.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | securityStatus inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SecurityStatus.encode_length]
    omega
  | mdIncrementalRefreshBook inner =>
    have bound_inner := MdIncrementalRefreshBook.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshDailyStatistics inner =>
    have bound_inner := MdIncrementalRefreshDailyStatistics.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshLimitsBanding inner =>
    have bound_inner := MdIncrementalRefreshLimitsBanding.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshSessionStatistics inner =>
    have bound_inner := MdIncrementalRefreshSessionStatistics.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshTrade inner =>
    have bound_inner := MdIncrementalRefreshTrade.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshVolume inner =>
    have bound_inner := MdIncrementalRefreshVolume.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | snapshotFullRefresh inner =>
    have bound_inner := SnapshotFullRefresh.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | quoteRequest inner =>
    have bound_inner := QuoteRequest.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | mdInstrumentDefinitionOption inner =>
    have bound_inner := MdInstrumentDefinitionOption.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshTradeSummary inner =>
    have bound_inner := MdIncrementalRefreshTradeSummary.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | negotiate inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Negotiate.encode_length]
    omega
  | negotiationReject inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, NegotiationReject.encode_length]
    omega
  | negotiationResponse inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, NegotiationResponse.encode_length]
    omega
  | terminate inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Terminate.encode_length]
    omega
  | marketDataRequest inner =>
    have bound_inner := MarketDataRequest.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | requestAck inner =>
    have bound_inner := RequestAck.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | requestReject inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RequestReject.encode_length]
    omega
  | securityListRequest inner =>
    have bound_inner := SecurityListRequest.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | securityStatusRequest inner =>
    have bound_inner := SecurityStatusRequest.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | subscriberHeartbeat inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SubscriberHeartbeat.encode_length]
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

/-- Udp Packet -/
structure UdpPacket where
  binaryPacketHeader : BinaryPacketHeader
  message : List Message
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  BinaryPacketHeader.encode message.binaryPacketHeader
    ++ (encodeMany Message.encode message.message)

def decode (bytes : List UInt8) : Option UdpPacket := do
  let (binaryPacketHeader, bytes) ← BinaryPacketHeader.decode bytes
  let message ← decodeAll Message.decode bytes.length bytes
  pure { binaryPacketHeader, message }

theorem encode_length_pos (message : UdpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [BinaryPacketHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : UdpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [BinaryPacketHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end UdpPacket

end Omi.CmeGlobexMdp3SbeV15Udp
