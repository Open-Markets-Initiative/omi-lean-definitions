import Wire

/-!
# TMX Group Sola Order Entry v1.21

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxMxSolaorderentrySailV121Firm

/-- User Connection Occurrence: 2 bytes -/
structure UserConnectionOccurrence where
  messageTypesToBeReceived : Alpha 2
  deriving DecidableEq, Repr

namespace UserConnectionOccurrence

def encode (message : UserConnectionOccurrence) : List UInt8 :=
  Alpha.encode message.messageTypesToBeReceived

def decode (bytes : List UInt8) : Option (UserConnectionOccurrence × List UInt8) := do
  let (messageTypesToBeReceived, bytes) ← Alpha.decode 2 bytes
  pure ({ messageTypesToBeReceived }, bytes)

@[simp] theorem encode_length (message : UserConnectionOccurrence) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : UserConnectionOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserConnectionOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserConnectionOccurrence

/-- User Connection -/
structure UserConnection where
  protocolId : Alpha 2
  userId : Alpha 8
  passwordMd5Encryption : Alpha 8
  sessionId : Alpha 4
  userMessageTimestampLocalHhmmss : Alpha 6
  exchangeMessageId : Alpha 6
  inactivityInterval : Alpha 2
  userConnectionOccurrence : Digited 2 UserConnectionOccurrence
  deriving DecidableEq, Repr

namespace UserConnection

def encode (message : UserConnection) : List UInt8 :=
  Alpha.encode message.protocolId
    ++ (Alpha.encode message.userId
    ++ (Alpha.encode message.passwordMd5Encryption
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.userMessageTimestampLocalHhmmss
    ++ (Alpha.encode message.exchangeMessageId
    ++ (Alpha.encode message.inactivityInterval
    ++ (encodeDigits 2 message.userConnectionOccurrence.val.length
    ++ (encodeMany UserConnectionOccurrence.encode message.userConnectionOccurrence.val))))))))

def decode (bytes : List UInt8) : Option (UserConnection × List UInt8) := do
  let (protocolId, bytes) ← Alpha.decode 2 bytes
  let (userId, bytes) ← Alpha.decode 8 bytes
  let (passwordMd5Encryption, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← Alpha.decode 4 bytes
  let (userMessageTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (exchangeMessageId, bytes) ← Alpha.decode 6 bytes
  let (inactivityInterval, bytes) ← Alpha.decode 2 bytes
  let (numberOfMessageTypesToBeReceived, bytes) ← decodeDigits 2 bytes
  let (userConnectionOccurrence_, bytes) ← decodeMany UserConnectionOccurrence.decode numberOfMessageTypesToBeReceived bytes
  if fits_userConnectionOccurrence : userConnectionOccurrence_.length < 10 ^ 2 then
    pure ({ protocolId, userId, passwordMd5Encryption, sessionId, userMessageTimestampLocalHhmmss, exchangeMessageId, inactivityInterval, userConnectionOccurrence := ⟨userConnectionOccurrence_, fits_userConnectionOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : UserConnection) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UserConnection) : (encode message).length ≤ 236 := by
  have bound_userConnectionOccurrence := message.userConnectionOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeDigits_length, encodeMany_length_const UserConnectionOccurrence.encode 2 UserConnectionOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : UserConnection) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.userConnectionOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany UserConnectionOccurrence.encode UserConnectionOccurrence.decode UserConnectionOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.userConnectionOccurrence.length_lt]
  rfl

end UserConnection

/-- Disconnection Instruction Occurrence: 10 bytes -/
structure DisconnectionInstructionOccurrence where
  traderId : Alpha 8
  disconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly : Alpha 1
  activeYOnNOff : Alpha 1
  deriving DecidableEq, Repr

namespace DisconnectionInstructionOccurrence

def encode (message : DisconnectionInstructionOccurrence) : List UInt8 :=
  Alpha.encode message.traderId
    ++ (Alpha.encode message.disconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly
    ++ (Alpha.encode message.activeYOnNOff))

def decode (bytes : List UInt8) : Option (DisconnectionInstructionOccurrence × List UInt8) := do
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (disconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly, bytes) ← Alpha.decode 1 bytes
  let (activeYOnNOff, bytes) ← Alpha.decode 1 bytes
  pure ({ traderId, disconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly, activeYOnNOff }, bytes)

@[simp] theorem encode_length (message : DisconnectionInstructionOccurrence) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : DisconnectionInstructionOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisconnectionInstructionOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DisconnectionInstructionOccurrence

/-- Disconnection Instruction -/
structure DisconnectionInstruction where
  disconnectionInstructionOccurrence : Digited 2 DisconnectionInstructionOccurrence
  deriving DecidableEq, Repr

namespace DisconnectionInstruction

def encode (message : DisconnectionInstruction) : List UInt8 :=
  encodeDigits 2 message.disconnectionInstructionOccurrence.val.length
    ++ (encodeMany DisconnectionInstructionOccurrence.encode message.disconnectionInstructionOccurrence.val)

def decode (bytes : List UInt8) : Option (DisconnectionInstruction × List UInt8) := do
  let (numberOfInstructionsPresentInTheMessage, bytes) ← decodeDigits 2 bytes
  let (disconnectionInstructionOccurrence_, bytes) ← decodeMany DisconnectionInstructionOccurrence.decode numberOfInstructionsPresentInTheMessage bytes
  if fits_disconnectionInstructionOccurrence : disconnectionInstructionOccurrence_.length < 10 ^ 2 then
    pure ({ disconnectionInstructionOccurrence := ⟨disconnectionInstructionOccurrence_, fits_disconnectionInstructionOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : DisconnectionInstruction) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeDigits_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DisconnectionInstruction) : (encode message).length ≤ 992 := by
  have bound_disconnectionInstructionOccurrence := message.disconnectionInstructionOccurrence.length_lt
  unfold encode
  simp only [List.length_append, encodeDigits_length, encodeMany_length_const DisconnectionInstructionOccurrence.encode 10 DisconnectionInstructionOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : DisconnectionInstruction) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.disconnectionInstructionOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany DisconnectionInstructionOccurrence.encode DisconnectionInstructionOccurrence.decode DisconnectionInstructionOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.disconnectionInstructionOccurrence.length_lt]
  rfl

end DisconnectionInstruction

/-- Heartbeat Response: 20 bytes -/
structure HeartbeatResponse where
  userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod : Alpha 8
  lastExchangeMessageIdSentToParticipant : Alpha 6
  userMessageTimestampLocalHhmmss : Alpha 6
  deriving DecidableEq, Repr

namespace HeartbeatResponse

def encode (message : HeartbeatResponse) : List UInt8 :=
  Alpha.encode message.userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod
    ++ (Alpha.encode message.lastExchangeMessageIdSentToParticipant
    ++ (Alpha.encode message.userMessageTimestampLocalHhmmss))

def decode (bytes : List UInt8) : Option (HeartbeatResponse × List UInt8) := do
  let (userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod, bytes) ← Alpha.decode 8 bytes
  let (lastExchangeMessageIdSentToParticipant, bytes) ← Alpha.decode 6 bytes
  let (userMessageTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  pure ({ userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod, lastExchangeMessageIdSentToParticipant, userMessageTimestampLocalHhmmss }, bytes)

@[simp] theorem encode_length (message : HeartbeatResponse) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : HeartbeatResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end HeartbeatResponse

/-- User Disconnection: 12 bytes -/
structure UserDisconnection where
  userId : Alpha 8
  sessionId : Alpha 4
  deriving DecidableEq, Repr

namespace UserDisconnection

def encode (message : UserDisconnection) : List UInt8 :=
  Alpha.encode message.userId
    ++ (Alpha.encode message.sessionId)

def decode (bytes : List UInt8) : Option (UserDisconnection × List UInt8) := do
  let (userId, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← Alpha.decode 4 bytes
  pure ({ userId, sessionId }, bytes)

@[simp] theorem encode_length (message : UserDisconnection) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : UserDisconnection) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserDisconnection) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserDisconnection

/-- Order Request: 0 bytes -/
structure OrderRequest where
  deriving DecidableEq, Repr

namespace OrderRequest

def encode (_ : OrderRequest) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (OrderRequest × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : OrderRequest) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : OrderRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end OrderRequest

/-- Incoming Messages Header: 22 bytes -/
structure IncomingMessagesHeader where
  userTimestampLocalHhmmss : Alpha 6
  traderId : Alpha 8
  userSequenceId : Alpha 8
  deriving DecidableEq, Repr

namespace IncomingMessagesHeader

def encode (message : IncomingMessagesHeader) : List UInt8 :=
  Alpha.encode message.userTimestampLocalHhmmss
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.userSequenceId))

def decode (bytes : List UInt8) : Option (IncomingMessagesHeader × List UInt8) := do
  let (userTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (userSequenceId, bytes) ← Alpha.decode 8 bytes
  pure ({ userTimestampLocalHhmmss, traderId, userSequenceId }, bytes)

@[simp] theorem encode_length (message : IncomingMessagesHeader) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : IncomingMessagesHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncomingMessagesHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IncomingMessagesHeader

/-- Clearing Data: 20 bytes -/
structure ClearingData where
  clearingInstruction : Alpha 12
  accountType : Alpha 1
  openClose : Alpha 1
  hedgeSpec : Alpha 1
  filler5 : Alpha 5
  deriving DecidableEq, Repr

namespace ClearingData

def encode (message : ClearingData) : List UInt8 :=
  Alpha.encode message.clearingInstruction
    ++ (Alpha.encode message.accountType
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.hedgeSpec
    ++ (Alpha.encode message.filler5))))

def decode (bytes : List UInt8) : Option (ClearingData × List UInt8) := do
  let (clearingInstruction, bytes) ← Alpha.decode 12 bytes
  let (accountType, bytes) ← Alpha.decode 1 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (hedgeSpec, bytes) ← Alpha.decode 1 bytes
  let (filler5, bytes) ← Alpha.decode 5 bytes
  pure ({ clearingInstruction, accountType, openClose, hedgeSpec, filler5 }, bytes)

@[simp] theorem encode_length (message : ClearingData) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ClearingData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClearingData

/-- Owner Data: 50 bytes -/
structure OwnerData where
  memo : Alpha 50
  deriving DecidableEq, Repr

namespace OwnerData

def encode (message : OwnerData) : List UInt8 :=
  Alpha.encode message.memo

def decode (bytes : List UInt8) : Option (OwnerData × List UInt8) := do
  let (memo, bytes) ← Alpha.decode 50 bytes
  pure ({ memo }, bytes)

@[simp] theorem encode_length (message : OwnerData) : (encode message).length = 50 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : OwnerData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OwnerData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end OwnerData

/-- Bulk Quote Data: 174 bytes -/
structure BulkQuoteData where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  clearingData : ClearingData
  ownerData : OwnerData
  maximumNumberTrades : Alpha 2
  minimumVolume : Alpha 8
  filler2 : Alpha 2
  calculationTimeInterval : Alpha 8
  maximumTotalVolume : Alpha 8
  maximumTotalValue : Alpha 8
  deltaMaximumVolume : Alpha 8
  deltaMaximumValue : Alpha 8
  antiWashId : Alpha 8
  filler20 : Alpha 20
  deriving DecidableEq, Repr

namespace BulkQuoteData

def encode (message : BulkQuoteData) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.maximumNumberTrades
    ++ (Alpha.encode message.minimumVolume
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.calculationTimeInterval
    ++ (Alpha.encode message.maximumTotalVolume
    ++ (Alpha.encode message.maximumTotalValue
    ++ (Alpha.encode message.deltaMaximumVolume
    ++ (Alpha.encode message.deltaMaximumValue
    ++ (Alpha.encode message.antiWashId
    ++ (Alpha.encode message.filler20)))))))))))))

def decode (bytes : List UInt8) : Option (BulkQuoteData × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (maximumNumberTrades, bytes) ← Alpha.decode 2 bytes
  let (minimumVolume, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (calculationTimeInterval, bytes) ← Alpha.decode 8 bytes
  let (maximumTotalVolume, bytes) ← Alpha.decode 8 bytes
  let (maximumTotalValue, bytes) ← Alpha.decode 8 bytes
  let (deltaMaximumVolume, bytes) ← Alpha.decode 8 bytes
  let (deltaMaximumValue, bytes) ← Alpha.decode 8 bytes
  let (antiWashId, bytes) ← Alpha.decode 8 bytes
  let (filler20, bytes) ← Alpha.decode 20 bytes
  pure ({ incomingMessagesHeader, group, clearingData, ownerData, maximumNumberTrades, minimumVolume, filler2, calculationTimeInterval, maximumTotalVolume, maximumTotalValue, deltaMaximumVolume, deltaMaximumValue, antiWashId, filler20 }, bytes)

@[simp] theorem encode_length (message : BulkQuoteData) : (encode message).length = 174 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : BulkQuoteData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuoteData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuoteData

/-- Firm Risk Config Trader Team Trader: 4 bytes -/
structure FirmRiskConfigTraderTeamTrader where
  trader : Alpha 4
  deriving DecidableEq, Repr

namespace FirmRiskConfigTraderTeamTrader

def encode (message : FirmRiskConfigTraderTeamTrader) : List UInt8 :=
  Alpha.encode message.trader

def decode (bytes : List UInt8) : Option (FirmRiskConfigTraderTeamTrader × List UInt8) := do
  let (trader, bytes) ← Alpha.decode 4 bytes
  pure ({ trader }, bytes)

@[simp] theorem encode_length (message : FirmRiskConfigTraderTeamTrader) : (encode message).length = 4 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : FirmRiskConfigTraderTeamTrader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FirmRiskConfigTraderTeamTrader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end FirmRiskConfigTraderTeamTrader

/-- Firm Risk Config Trader Team -/
structure FirmRiskConfigTraderTeam where
  teamLevelRiskOption : Alpha 1
  firmRiskConfigTraderTeamTrader : Digited 3 FirmRiskConfigTraderTeamTrader
  deriving DecidableEq, Repr

namespace FirmRiskConfigTraderTeam

def encode (message : FirmRiskConfigTraderTeam) : List UInt8 :=
  Alpha.encode message.teamLevelRiskOption
    ++ (encodeDigits 3 message.firmRiskConfigTraderTeamTrader.val.length
    ++ (encodeMany FirmRiskConfigTraderTeamTrader.encode message.firmRiskConfigTraderTeamTrader.val))

def decode (bytes : List UInt8) : Option (FirmRiskConfigTraderTeam × List UInt8) := do
  let (teamLevelRiskOption, bytes) ← Alpha.decode 1 bytes
  let (numberOfTradersInTeam, bytes) ← decodeDigits 3 bytes
  let (firmRiskConfigTraderTeamTrader_, bytes) ← decodeMany FirmRiskConfigTraderTeamTrader.decode numberOfTradersInTeam bytes
  if fits_firmRiskConfigTraderTeamTrader : firmRiskConfigTraderTeamTrader_.length < 10 ^ 3 then
    pure ({ teamLevelRiskOption, firmRiskConfigTraderTeamTrader := ⟨firmRiskConfigTraderTeamTrader_, fits_firmRiskConfigTraderTeamTrader⟩ }, bytes)
  else none

theorem encode_length_pos (message : FirmRiskConfigTraderTeam) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FirmRiskConfigTraderTeam) : (encode message).length ≤ 4000 := by
  have bound_firmRiskConfigTraderTeamTrader := message.firmRiskConfigTraderTeamTrader.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeDigits_length, encodeMany_length_const FirmRiskConfigTraderTeamTrader.encode 4 FirmRiskConfigTraderTeamTrader.encode_length]
  omega

@[simp] theorem decode_encode (message : FirmRiskConfigTraderTeam) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.firmRiskConfigTraderTeamTrader.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany FirmRiskConfigTraderTeamTrader.encode FirmRiskConfigTraderTeamTrader.decode FirmRiskConfigTraderTeamTrader.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.firmRiskConfigTraderTeamTrader.length_lt]
  rfl

end FirmRiskConfigTraderTeam

/-- Firm Risk Config -/
structure FirmRiskConfig where
  incomingMessagesHeader : IncomingMessagesHeader
  firmLevelRiskOption : Alpha 1
  firmRiskConfigTraderTeam : Digited 3 FirmRiskConfigTraderTeam
  deriving DecidableEq, Repr

namespace FirmRiskConfig

def encode (message : FirmRiskConfig) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.firmLevelRiskOption
    ++ (encodeDigits 3 message.firmRiskConfigTraderTeam.val.length
    ++ (encodeMany FirmRiskConfigTraderTeam.encode message.firmRiskConfigTraderTeam.val)))

def decode (bytes : List UInt8) : Option (FirmRiskConfig × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (firmLevelRiskOption, bytes) ← Alpha.decode 1 bytes
  let (numberOfTraderTeams, bytes) ← decodeDigits 3 bytes
  let (firmRiskConfigTraderTeam_, bytes) ← decodeMany FirmRiskConfigTraderTeam.decode numberOfTraderTeams bytes
  if fits_firmRiskConfigTraderTeam : firmRiskConfigTraderTeam_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, firmLevelRiskOption, firmRiskConfigTraderTeam := ⟨firmRiskConfigTraderTeam_, fits_firmRiskConfigTraderTeam⟩ }, bytes)
  else none

theorem encode_length_pos (message : FirmRiskConfig) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FirmRiskConfig) : (encode message).length ≤ 3996026 := by
  have bound_firmRiskConfigTraderTeam := message.firmRiskConfigTraderTeam.length_lt
  have bound_firmRiskConfigTraderTeam_items := encodeMany_length_le FirmRiskConfigTraderTeam.encode 4000 FirmRiskConfigTraderTeam.encode_length_le message.firmRiskConfigTraderTeam.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length]
  omega

@[simp] theorem decode_encode (message : FirmRiskConfig) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.firmRiskConfigTraderTeam.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany FirmRiskConfigTraderTeam.encode FirmRiskConfigTraderTeam.decode FirmRiskConfigTraderTeam.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.firmRiskConfigTraderTeam.length_lt]
  rfl

end FirmRiskConfig

/-- Global Cancellation: 25 bytes -/
structure GlobalCancellation where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  typeOfCancellationQQuotesOnly : Alpha 1
  deriving DecidableEq, Repr

namespace GlobalCancellation

def encode (message : GlobalCancellation) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.typeOfCancellationQQuotesOnly))

def decode (bytes : List UInt8) : Option (GlobalCancellation × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (typeOfCancellationQQuotesOnly, bytes) ← Alpha.decode 1 bytes
  pure ({ incomingMessagesHeader, group, typeOfCancellationQQuotesOnly }, bytes)

@[simp] theorem encode_length (message : GlobalCancellation) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : GlobalCancellation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GlobalCancellation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GlobalCancellation

/-- User Global Cancellation: 37 bytes -/
structure UserGlobalCancellation where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  typeOfCancellation : Alpha 1
  accountTypeFilter : Alpha 8
  deriving DecidableEq, Repr

namespace UserGlobalCancellation

def encode (message : UserGlobalCancellation) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.typeOfCancellation
    ++ (Alpha.encode message.accountTypeFilter))))

def decode (bytes : List UInt8) : Option (UserGlobalCancellation × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (typeOfCancellation, bytes) ← Alpha.decode 1 bytes
  let (accountTypeFilter, bytes) ← Alpha.decode 8 bytes
  pure ({ incomingMessagesHeader, group, instrument, typeOfCancellation, accountTypeFilter }, bytes)

@[simp] theorem encode_length (message : UserGlobalCancellation) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : UserGlobalCancellation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserGlobalCancellation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserGlobalCancellation

/-- Set Group Risk Limits Occurrence: 76 bytes -/
structure SetGroupRiskLimitsOccurrence where
  trader : Alpha 4
  group : Alpha 2
  netExposureAction : Alpha 1
  longExposureAction : Alpha 1
  shortExposureAction : Alpha 1
  netPositionAction : Alpha 1
  longPositionAction : Alpha 1
  shortPositionAction : Alpha 1
  maximumOrderQuantity : Alpha 8
  netPositionLimit : Alpha 8
  longPositionLimit : Alpha 8
  shortPositionLimit : Alpha 8
  netExposureLimit : Alpha 10
  longExposureLimit : Alpha 10
  shortExposureLimit : Alpha 10
  filler2 : Alpha 2
  deriving DecidableEq, Repr

namespace SetGroupRiskLimitsOccurrence

def encode (message : SetGroupRiskLimitsOccurrence) : List UInt8 :=
  Alpha.encode message.trader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.netExposureAction
    ++ (Alpha.encode message.longExposureAction
    ++ (Alpha.encode message.shortExposureAction
    ++ (Alpha.encode message.netPositionAction
    ++ (Alpha.encode message.longPositionAction
    ++ (Alpha.encode message.shortPositionAction
    ++ (Alpha.encode message.maximumOrderQuantity
    ++ (Alpha.encode message.netPositionLimit
    ++ (Alpha.encode message.longPositionLimit
    ++ (Alpha.encode message.shortPositionLimit
    ++ (Alpha.encode message.netExposureLimit
    ++ (Alpha.encode message.longExposureLimit
    ++ (Alpha.encode message.shortExposureLimit
    ++ (Alpha.encode message.filler2)))))))))))))))

def decode (bytes : List UInt8) : Option (SetGroupRiskLimitsOccurrence × List UInt8) := do
  let (trader, bytes) ← Alpha.decode 4 bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (netExposureAction, bytes) ← Alpha.decode 1 bytes
  let (longExposureAction, bytes) ← Alpha.decode 1 bytes
  let (shortExposureAction, bytes) ← Alpha.decode 1 bytes
  let (netPositionAction, bytes) ← Alpha.decode 1 bytes
  let (longPositionAction, bytes) ← Alpha.decode 1 bytes
  let (shortPositionAction, bytes) ← Alpha.decode 1 bytes
  let (maximumOrderQuantity, bytes) ← Alpha.decode 8 bytes
  let (netPositionLimit, bytes) ← Alpha.decode 8 bytes
  let (longPositionLimit, bytes) ← Alpha.decode 8 bytes
  let (shortPositionLimit, bytes) ← Alpha.decode 8 bytes
  let (netExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (longExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (shortExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  pure ({ trader, group, netExposureAction, longExposureAction, shortExposureAction, netPositionAction, longPositionAction, shortPositionAction, maximumOrderQuantity, netPositionLimit, longPositionLimit, shortPositionLimit, netExposureLimit, longExposureLimit, shortExposureLimit, filler2 }, bytes)

@[simp] theorem encode_length (message : SetGroupRiskLimitsOccurrence) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SetGroupRiskLimitsOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SetGroupRiskLimitsOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SetGroupRiskLimitsOccurrence

/-- Set Group Risk Limits -/
structure SetGroupRiskLimits where
  incomingMessagesHeader : IncomingMessagesHeader
  resetAllGroups : Alpha 1
  setGroupRiskLimitsOccurrence : Digited 3 SetGroupRiskLimitsOccurrence
  deriving DecidableEq, Repr

namespace SetGroupRiskLimits

def encode (message : SetGroupRiskLimits) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.resetAllGroups
    ++ (encodeDigits 3 message.setGroupRiskLimitsOccurrence.val.length
    ++ (encodeMany SetGroupRiskLimitsOccurrence.encode message.setGroupRiskLimitsOccurrence.val)))

def decode (bytes : List UInt8) : Option (SetGroupRiskLimits × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (resetAllGroups, bytes) ← Alpha.decode 1 bytes
  let (numberOfGroupLimits, bytes) ← decodeDigits 3 bytes
  let (setGroupRiskLimitsOccurrence_, bytes) ← decodeMany SetGroupRiskLimitsOccurrence.decode numberOfGroupLimits bytes
  if fits_setGroupRiskLimitsOccurrence : setGroupRiskLimitsOccurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, resetAllGroups, setGroupRiskLimitsOccurrence := ⟨setGroupRiskLimitsOccurrence_, fits_setGroupRiskLimitsOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : SetGroupRiskLimits) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SetGroupRiskLimits) : (encode message).length ≤ 75950 := by
  have bound_setGroupRiskLimitsOccurrence := message.setGroupRiskLimitsOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const SetGroupRiskLimitsOccurrence.encode 76 SetGroupRiskLimitsOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : SetGroupRiskLimits) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.setGroupRiskLimitsOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany SetGroupRiskLimitsOccurrence.encode SetGroupRiskLimitsOccurrence.decode SetGroupRiskLimitsOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.setGroupRiskLimitsOccurrence.length_lt]
  rfl

end SetGroupRiskLimits

/-- Set Global Risk Limits: 101 bytes -/
structure SetGlobalRiskLimits where
  incomingMessagesHeader : IncomingMessagesHeader
  globalNetExposureAction : Alpha 1
  defaultNetExposureAction : Alpha 1
  defaultLongExposureAction : Alpha 1
  defaultShortExposureAction : Alpha 1
  defaultNetPositionAction : Alpha 1
  defaultLongPositionAction : Alpha 1
  defaultShortPositionAction : Alpha 1
  globalNetExposureLimit : Alpha 10
  defaultMaximumOrderQuantity : Alpha 8
  defaultNetExposureLimit : Alpha 10
  defaultLongExposureLimit : Alpha 10
  defaultShortExposureLimit : Alpha 10
  defaultNetPositionLimit : Alpha 8
  defaultLongPositionLimit : Alpha 8
  defaultShortPositionLimit : Alpha 8
  deriving DecidableEq, Repr

namespace SetGlobalRiskLimits

def encode (message : SetGlobalRiskLimits) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.globalNetExposureAction
    ++ (Alpha.encode message.defaultNetExposureAction
    ++ (Alpha.encode message.defaultLongExposureAction
    ++ (Alpha.encode message.defaultShortExposureAction
    ++ (Alpha.encode message.defaultNetPositionAction
    ++ (Alpha.encode message.defaultLongPositionAction
    ++ (Alpha.encode message.defaultShortPositionAction
    ++ (Alpha.encode message.globalNetExposureLimit
    ++ (Alpha.encode message.defaultMaximumOrderQuantity
    ++ (Alpha.encode message.defaultNetExposureLimit
    ++ (Alpha.encode message.defaultLongExposureLimit
    ++ (Alpha.encode message.defaultShortExposureLimit
    ++ (Alpha.encode message.defaultNetPositionLimit
    ++ (Alpha.encode message.defaultLongPositionLimit
    ++ (Alpha.encode message.defaultShortPositionLimit)))))))))))))))

def decode (bytes : List UInt8) : Option (SetGlobalRiskLimits × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (globalNetExposureAction, bytes) ← Alpha.decode 1 bytes
  let (defaultNetExposureAction, bytes) ← Alpha.decode 1 bytes
  let (defaultLongExposureAction, bytes) ← Alpha.decode 1 bytes
  let (defaultShortExposureAction, bytes) ← Alpha.decode 1 bytes
  let (defaultNetPositionAction, bytes) ← Alpha.decode 1 bytes
  let (defaultLongPositionAction, bytes) ← Alpha.decode 1 bytes
  let (defaultShortPositionAction, bytes) ← Alpha.decode 1 bytes
  let (globalNetExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (defaultMaximumOrderQuantity, bytes) ← Alpha.decode 8 bytes
  let (defaultNetExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (defaultLongExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (defaultShortExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (defaultNetPositionLimit, bytes) ← Alpha.decode 8 bytes
  let (defaultLongPositionLimit, bytes) ← Alpha.decode 8 bytes
  let (defaultShortPositionLimit, bytes) ← Alpha.decode 8 bytes
  pure ({ incomingMessagesHeader, globalNetExposureAction, defaultNetExposureAction, defaultLongExposureAction, defaultShortExposureAction, defaultNetPositionAction, defaultLongPositionAction, defaultShortPositionAction, globalNetExposureLimit, defaultMaximumOrderQuantity, defaultNetExposureLimit, defaultLongExposureLimit, defaultShortExposureLimit, defaultNetPositionLimit, defaultLongPositionLimit, defaultShortPositionLimit }, bytes)

@[simp] theorem encode_length (message : SetGlobalRiskLimits) : (encode message).length = 101 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : SetGlobalRiskLimits) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SetGlobalRiskLimits) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SetGlobalRiskLimits

/-- Order Entry: 181 bytes -/
structure OrderEntry where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  priceType : Alpha 1
  verbSide : Alpha 1
  quantity : Alpha 8
  price : Alpha 10
  specialPriceTerm : Alpha 1
  additionalPrice : Alpha 10
  quantityTerm : Alpha 1
  additionalQuantity : Alpha 8
  durationType : Alpha 1
  gtdDate : Alpha 8
  executingParticipant : Alpha 4
  filler1 : Alpha 1
  clearingData : ClearingData
  ownerData : OwnerData
  antiWashId : Alpha 8
  antiWashInstruction : Alpha 1
  filler20 : Alpha 20
  deriving DecidableEq, Repr

namespace OrderEntry

def encode (message : OrderEntry) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.priceType
    ++ (Alpha.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.specialPriceTerm
    ++ (Alpha.encode message.additionalPrice
    ++ (Alpha.encode message.quantityTerm
    ++ (Alpha.encode message.additionalQuantity
    ++ (Alpha.encode message.durationType
    ++ (Alpha.encode message.gtdDate
    ++ (Alpha.encode message.executingParticipant
    ++ (Alpha.encode message.filler1
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.antiWashId
    ++ (Alpha.encode message.antiWashInstruction
    ++ (Alpha.encode message.filler20)))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderEntry × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (priceType, bytes) ← Alpha.decode 1 bytes
  let (verbSide, bytes) ← Alpha.decode 1 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (specialPriceTerm, bytes) ← Alpha.decode 1 bytes
  let (additionalPrice, bytes) ← Alpha.decode 10 bytes
  let (quantityTerm, bytes) ← Alpha.decode 1 bytes
  let (additionalQuantity, bytes) ← Alpha.decode 8 bytes
  let (durationType, bytes) ← Alpha.decode 1 bytes
  let (gtdDate, bytes) ← Alpha.decode 8 bytes
  let (executingParticipant, bytes) ← Alpha.decode 4 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (antiWashId, bytes) ← Alpha.decode 8 bytes
  let (antiWashInstruction, bytes) ← Alpha.decode 1 bytes
  let (filler20, bytes) ← Alpha.decode 20 bytes
  pure ({ incomingMessagesHeader, group, instrument, priceType, verbSide, quantity, price, specialPriceTerm, additionalPrice, quantityTerm, additionalQuantity, durationType, gtdDate, executingParticipant, filler1, clearingData, ownerData, antiWashId, antiWashInstruction, filler20 }, bytes)

@[simp] theorem encode_length (message : OrderEntry) : (encode message).length = 181 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderEntry

/-- Order Modification: 190 bytes -/
structure OrderModification where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  priceType : Alpha 1
  verbSide : Alpha 1
  quantitySign : Alpha 1
  quantity : Alpha 8
  price : Alpha 10
  specialPriceTerm : Alpha 1
  additionalPrice : Alpha 10
  quantityTerm : Alpha 1
  additionalQuantity : Alpha 8
  durationType : Alpha 1
  gtdDate : Alpha 8
  filler4 : Alpha 4
  filler1 : Alpha 1
  modifiedOrderId : Alpha 8
  clearingData : ClearingData
  ownerData : OwnerData
  antiWashId : Alpha 8
  antiWashInstruction : Alpha 1
  filler20 : Alpha 20
  deriving DecidableEq, Repr

namespace OrderModification

def encode (message : OrderModification) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.priceType
    ++ (Alpha.encode message.verbSide
    ++ (Alpha.encode message.quantitySign
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.specialPriceTerm
    ++ (Alpha.encode message.additionalPrice
    ++ (Alpha.encode message.quantityTerm
    ++ (Alpha.encode message.additionalQuantity
    ++ (Alpha.encode message.durationType
    ++ (Alpha.encode message.gtdDate
    ++ (Alpha.encode message.filler4
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.modifiedOrderId
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.antiWashId
    ++ (Alpha.encode message.antiWashInstruction
    ++ (Alpha.encode message.filler20)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderModification × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (priceType, bytes) ← Alpha.decode 1 bytes
  let (verbSide, bytes) ← Alpha.decode 1 bytes
  let (quantitySign, bytes) ← Alpha.decode 1 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (specialPriceTerm, bytes) ← Alpha.decode 1 bytes
  let (additionalPrice, bytes) ← Alpha.decode 10 bytes
  let (quantityTerm, bytes) ← Alpha.decode 1 bytes
  let (additionalQuantity, bytes) ← Alpha.decode 8 bytes
  let (durationType, bytes) ← Alpha.decode 1 bytes
  let (gtdDate, bytes) ← Alpha.decode 8 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (modifiedOrderId, bytes) ← Alpha.decode 8 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (antiWashId, bytes) ← Alpha.decode 8 bytes
  let (antiWashInstruction, bytes) ← Alpha.decode 1 bytes
  let (filler20, bytes) ← Alpha.decode 20 bytes
  pure ({ incomingMessagesHeader, group, instrument, priceType, verbSide, quantitySign, quantity, price, specialPriceTerm, additionalPrice, quantityTerm, additionalQuantity, durationType, gtdDate, filler4, filler1, modifiedOrderId, clearingData, ownerData, antiWashId, antiWashInstruction, filler20 }, bytes)

@[simp] theorem encode_length (message : OrderModification) : (encode message).length = 190 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderModification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModification

/-- New Strategy Instrument Leg Definition Repeating Block: 16 bytes -/
structure NewStrategyInstrumentLegDefinitionRepeatingBlock where
  legGroup : Alpha 2
  legInstrument : Alpha 4
  legVerb : Alpha 1
  filler1 : Alpha 1
  legQuantityRatio : Alpha 8
  deriving DecidableEq, Repr

namespace NewStrategyInstrumentLegDefinitionRepeatingBlock

def encode (message : NewStrategyInstrumentLegDefinitionRepeatingBlock) : List UInt8 :=
  Alpha.encode message.legGroup
    ++ (Alpha.encode message.legInstrument
    ++ (Alpha.encode message.legVerb
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.legQuantityRatio))))

def decode (bytes : List UInt8) : Option (NewStrategyInstrumentLegDefinitionRepeatingBlock × List UInt8) := do
  let (legGroup, bytes) ← Alpha.decode 2 bytes
  let (legInstrument, bytes) ← Alpha.decode 4 bytes
  let (legVerb, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (legQuantityRatio, bytes) ← Alpha.decode 8 bytes
  pure ({ legGroup, legInstrument, legVerb, filler1, legQuantityRatio }, bytes)

@[simp] theorem encode_length (message : NewStrategyInstrumentLegDefinitionRepeatingBlock) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : NewStrategyInstrumentLegDefinitionRepeatingBlock) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewStrategyInstrumentLegDefinitionRepeatingBlock) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewStrategyInstrumentLegDefinitionRepeatingBlock

/-- New Strategy Instrument -/
structure NewStrategyInstrument where
  incomingMessagesHeader : IncomingMessagesHeader
  newStrategyInstrumentLegDefinitionRepeatingBlock : Digited 2 NewStrategyInstrumentLegDefinitionRepeatingBlock
  deriving DecidableEq, Repr

namespace NewStrategyInstrument

def encode (message : NewStrategyInstrument) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (encodeDigits 2 message.newStrategyInstrumentLegDefinitionRepeatingBlock.val.length
    ++ (encodeMany NewStrategyInstrumentLegDefinitionRepeatingBlock.encode message.newStrategyInstrumentLegDefinitionRepeatingBlock.val))

def decode (bytes : List UInt8) : Option (NewStrategyInstrument × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (numberOfLegs, bytes) ← decodeDigits 2 bytes
  let (newStrategyInstrumentLegDefinitionRepeatingBlock_, bytes) ← decodeMany NewStrategyInstrumentLegDefinitionRepeatingBlock.decode numberOfLegs bytes
  if fits_newStrategyInstrumentLegDefinitionRepeatingBlock : newStrategyInstrumentLegDefinitionRepeatingBlock_.length < 10 ^ 2 then
    pure ({ incomingMessagesHeader, newStrategyInstrumentLegDefinitionRepeatingBlock := ⟨newStrategyInstrumentLegDefinitionRepeatingBlock_, fits_newStrategyInstrumentLegDefinitionRepeatingBlock⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewStrategyInstrument) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewStrategyInstrument) : (encode message).length ≤ 1608 := by
  have bound_newStrategyInstrumentLegDefinitionRepeatingBlock := message.newStrategyInstrumentLegDefinitionRepeatingBlock.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, encodeDigits_length, encodeMany_length_const NewStrategyInstrumentLegDefinitionRepeatingBlock.encode 16 NewStrategyInstrumentLegDefinitionRepeatingBlock.encode_length]
  omega

@[simp] theorem decode_encode (message : NewStrategyInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.newStrategyInstrumentLegDefinitionRepeatingBlock.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany NewStrategyInstrumentLegDefinitionRepeatingBlock.encode NewStrategyInstrumentLegDefinitionRepeatingBlock.decode NewStrategyInstrumentLegDefinitionRepeatingBlock.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.newStrategyInstrumentLegDefinitionRepeatingBlock.length_lt]
  rfl

end NewStrategyInstrument

/-- Buying Clearing Data: 20 bytes -/
structure BuyingClearingData where
  clearingInstruction : Alpha 12
  accountType : Alpha 1
  openClose : Alpha 1
  hedgeSpec : Alpha 1
  filler5 : Alpha 5
  deriving DecidableEq, Repr

namespace BuyingClearingData

def encode (message : BuyingClearingData) : List UInt8 :=
  Alpha.encode message.clearingInstruction
    ++ (Alpha.encode message.accountType
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.hedgeSpec
    ++ (Alpha.encode message.filler5))))

def decode (bytes : List UInt8) : Option (BuyingClearingData × List UInt8) := do
  let (clearingInstruction, bytes) ← Alpha.decode 12 bytes
  let (accountType, bytes) ← Alpha.decode 1 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (hedgeSpec, bytes) ← Alpha.decode 1 bytes
  let (filler5, bytes) ← Alpha.decode 5 bytes
  pure ({ clearingInstruction, accountType, openClose, hedgeSpec, filler5 }, bytes)

@[simp] theorem encode_length (message : BuyingClearingData) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BuyingClearingData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BuyingClearingData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BuyingClearingData

/-- Selling Clearing Data: 20 bytes -/
structure SellingClearingData where
  clearingInstruction : Alpha 12
  accountType : Alpha 1
  openClose : Alpha 1
  hedgeSpec : Alpha 1
  filler5 : Alpha 5
  deriving DecidableEq, Repr

namespace SellingClearingData

def encode (message : SellingClearingData) : List UInt8 :=
  Alpha.encode message.clearingInstruction
    ++ (Alpha.encode message.accountType
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.hedgeSpec
    ++ (Alpha.encode message.filler5))))

def decode (bytes : List UInt8) : Option (SellingClearingData × List UInt8) := do
  let (clearingInstruction, bytes) ← Alpha.decode 12 bytes
  let (accountType, bytes) ← Alpha.decode 1 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (hedgeSpec, bytes) ← Alpha.decode 1 bytes
  let (filler5, bytes) ← Alpha.decode 5 bytes
  pure ({ clearingInstruction, accountType, openClose, hedgeSpec, filler5 }, bytes)

@[simp] theorem encode_length (message : SellingClearingData) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SellingClearingData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SellingClearingData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SellingClearingData

/-- Buying Owner Data: 50 bytes -/
structure BuyingOwnerData where
  memo : Alpha 50
  deriving DecidableEq, Repr

namespace BuyingOwnerData

def encode (message : BuyingOwnerData) : List UInt8 :=
  Alpha.encode message.memo

def decode (bytes : List UInt8) : Option (BuyingOwnerData × List UInt8) := do
  let (memo, bytes) ← Alpha.decode 50 bytes
  pure ({ memo }, bytes)

@[simp] theorem encode_length (message : BuyingOwnerData) : (encode message).length = 50 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : BuyingOwnerData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BuyingOwnerData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end BuyingOwnerData

/-- Selling Owner Data: 50 bytes -/
structure SellingOwnerData where
  memo : Alpha 50
  deriving DecidableEq, Repr

namespace SellingOwnerData

def encode (message : SellingOwnerData) : List UInt8 :=
  Alpha.encode message.memo

def decode (bytes : List UInt8) : Option (SellingOwnerData × List UInt8) := do
  let (memo, bytes) ← Alpha.decode 50 bytes
  pure ({ memo }, bytes)

@[simp] theorem encode_length (message : SellingOwnerData) : (encode message).length = 50 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SellingOwnerData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SellingOwnerData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end SellingOwnerData

/-- Cross Entry: 207 bytes -/
structure CrossEntry where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  filler1 : Alpha 1
  quantity : Alpha 8
  price : Alpha 10
  buyingClearingData : BuyingClearingData
  sellingClearingData : SellingClearingData
  buyingOwnerData : BuyingOwnerData
  sellingOwnerData : SellingOwnerData
  filler20 : Alpha 20
  deriving DecidableEq, Repr

namespace CrossEntry

def encode (message : CrossEntry) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price
    ++ (BuyingClearingData.encode message.buyingClearingData
    ++ (SellingClearingData.encode message.sellingClearingData
    ++ (BuyingOwnerData.encode message.buyingOwnerData
    ++ (SellingOwnerData.encode message.sellingOwnerData
    ++ (Alpha.encode message.filler20))))))))))

def decode (bytes : List UInt8) : Option (CrossEntry × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (buyingClearingData, bytes) ← BuyingClearingData.decode bytes
  let (sellingClearingData, bytes) ← SellingClearingData.decode bytes
  let (buyingOwnerData, bytes) ← BuyingOwnerData.decode bytes
  let (sellingOwnerData, bytes) ← SellingOwnerData.decode bytes
  let (filler20, bytes) ← Alpha.decode 20 bytes
  pure ({ incomingMessagesHeader, group, instrument, filler1, quantity, price, buyingClearingData, sellingClearingData, buyingOwnerData, sellingOwnerData, filler20 }, bytes)

@[simp] theorem encode_length (message : CrossEntry) : (encode message).length = 207 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length, BuyingClearingData.encode_length, SellingClearingData.encode_length, BuyingOwnerData.encode_length, SellingOwnerData.encode_length]

theorem encode_length_pos (message : CrossEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuyingClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellingClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuyingOwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellingOwnerData.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CrossEntry

/-- Bulk Quote Occurrence: 26 bytes -/
structure BulkQuoteOccurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : Alpha 1
  quantitySignOr : Alpha 1
  quantity : Alpha 8
  price : Alpha 10
  deriving DecidableEq, Repr

namespace BulkQuoteOccurrence

def encode (message : BulkQuoteOccurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.verbSide
    ++ (Alpha.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price)))))

def decode (bytes : List UInt8) : Option (BulkQuoteOccurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← Alpha.decode 1 bytes
  let (quantitySignOr, bytes) ← Alpha.decode 1 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity, price }, bytes)

@[simp] theorem encode_length (message : BulkQuoteOccurrence) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BulkQuoteOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuoteOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuoteOccurrence

/-- Bulk Quote -/
structure BulkQuote where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuoteOccurrence : Digited 3 BulkQuoteOccurrence
  deriving DecidableEq, Repr

namespace BulkQuote

def encode (message : BulkQuote) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuoteOccurrence.val.length
    ++ (encodeMany BulkQuoteOccurrence.encode message.bulkQuoteOccurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuote × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuoteOccurrence_, bytes) ← decodeMany BulkQuoteOccurrence.decode numberOfQuotes bytes
  if fits_bulkQuoteOccurrence : bulkQuoteOccurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuoteOccurrence := ⟨bulkQuoteOccurrence_, fits_bulkQuoteOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuote) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuote) : (encode message).length ≤ 26009 := by
  have bound_bulkQuoteOccurrence := message.bulkQuoteOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuoteOccurrence.encode 26 BulkQuoteOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuoteOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuoteOccurrence.encode BulkQuoteOccurrence.decode BulkQuoteOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuoteOccurrence.length_lt]
  rfl

end BulkQuote

/-- Sail Request For Quote With Side: 37 bytes -/
structure SailRequestForQuoteWithSide where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  quantity : Alpha 8
  marketSide : Alpha 1
  deriving DecidableEq, Repr

namespace SailRequestForQuoteWithSide

def encode (message : SailRequestForQuoteWithSide) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.marketSide))))

def decode (bytes : List UInt8) : Option (SailRequestForQuoteWithSide × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (marketSide, bytes) ← Alpha.decode 1 bytes
  pure ({ incomingMessagesHeader, group, instrument, quantity, marketSide }, bytes)

@[simp] theorem encode_length (message : SailRequestForQuoteWithSide) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : SailRequestForQuoteWithSide) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SailRequestForQuoteWithSide) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SailRequestForQuoteWithSide

/-- Bulk Quote Participant Bqp Protection Subscription: 25 bytes -/
structure BulkQuoteParticipantBqpProtectionSubscription where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  protectionTypeAdvancedProtectionAdvancedProtectionDisabled : Alpha 1
  deriving DecidableEq, Repr

namespace BulkQuoteParticipantBqpProtectionSubscription

def encode (message : BulkQuoteParticipantBqpProtectionSubscription) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.protectionTypeAdvancedProtectionAdvancedProtectionDisabled))

def decode (bytes : List UInt8) : Option (BulkQuoteParticipantBqpProtectionSubscription × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (protectionTypeAdvancedProtectionAdvancedProtectionDisabled, bytes) ← Alpha.decode 1 bytes
  pure ({ incomingMessagesHeader, group, protectionTypeAdvancedProtectionAdvancedProtectionDisabled }, bytes)

@[simp] theorem encode_length (message : BulkQuoteParticipantBqpProtectionSubscription) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : BulkQuoteParticipantBqpProtectionSubscription) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuoteParticipantBqpProtectionSubscription) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuoteParticipantBqpProtectionSubscription

/-- Request For Quote: 36 bytes -/
structure RequestForQuote where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  quantity : Alpha 8
  deriving DecidableEq, Repr

namespace RequestForQuote

def encode (message : RequestForQuote) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.quantity)))

def decode (bytes : List UInt8) : Option (RequestForQuote × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  pure ({ incomingMessagesHeader, group, instrument, quantity }, bytes)

@[simp] theorem encode_length (message : RequestForQuote) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RequestForQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestForQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RequestForQuote

/-- Order Cancellation: 36 bytes -/
structure OrderCancellation where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  cancelledOrderId : Alpha 8
  deriving DecidableEq, Repr

namespace OrderCancellation

def encode (message : OrderCancellation) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.cancelledOrderId)))

def decode (bytes : List UInt8) : Option (OrderCancellation × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (cancelledOrderId, bytes) ← Alpha.decode 8 bytes
  pure ({ incomingMessagesHeader, group, instrument, cancelledOrderId }, bytes)

@[simp] theorem encode_length (message : OrderCancellation) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderCancellation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancellation

/-- Any Firm Message, selected by Message Type -/
inductive FirmMessage where
  | userConnection (message : UserConnection) -- "TC" 0x5443
  | disconnectionInstruction (message : DisconnectionInstruction) -- "TA" 0x5441
  | heartbeatResponse (message : HeartbeatResponse) -- "TI" 0x5449
  | userDisconnection (message : UserDisconnection) -- "TD" 0x5444
  | orderRequest (message : OrderRequest) -- "AF" 0x4146
  | bulkQuoteData (message : BulkQuoteData) -- "BD" 0x4244
  | firmRiskConfig (message : FirmRiskConfig) -- "CR" 0x4352
  | globalCancellation (message : GlobalCancellation) -- "GC" 0x4743
  | userGlobalCancellation (message : UserGlobalCancellation) -- "GZ" 0x475A
  | setGroupRiskLimits (message : SetGroupRiskLimits) -- "MK" 0x4D4B
  | setGlobalRiskLimits (message : SetGlobalRiskLimits) -- "ML" 0x4D4C
  | orderEntry (message : OrderEntry) -- "OE" 0x4F45
  | orderModification (message : OrderModification) -- "OM" 0x4F4D
  | newStrategyInstrument (message : NewStrategyInstrument) -- "ON" 0x4F4E
  | crossEntry (message : CrossEntry) -- "OX" 0x4F58
  | bulkQuote (message : BulkQuote) -- "QP" 0x5150
  | sailRequestForQuoteWithSide (message : SailRequestForQuoteWithSide) -- "QS" 0x5153
  | bulkQuoteParticipantBqpProtectionSubscription (message : BulkQuoteParticipantBqpProtectionSubscription) -- "RP" 0x5250
  | requestForQuote (message : RequestForQuote) -- "RQ" 0x5251
  | orderCancellation (message : OrderCancellation) -- "XE" 0x5845
  deriving DecidableEq, Repr

namespace FirmMessage

/-- The Message Type each message is sent under -/
def tag : FirmMessage → BitVec 16
  | .userConnection _ => 21571
  | .disconnectionInstruction _ => 21569
  | .heartbeatResponse _ => 21577
  | .userDisconnection _ => 21572
  | .orderRequest _ => 16710
  | .bulkQuoteData _ => 16964
  | .firmRiskConfig _ => 17234
  | .globalCancellation _ => 18243
  | .userGlobalCancellation _ => 18266
  | .setGroupRiskLimits _ => 19787
  | .setGlobalRiskLimits _ => 19788
  | .orderEntry _ => 20293
  | .orderModification _ => 20301
  | .newStrategyInstrument _ => 20302
  | .crossEntry _ => 20312
  | .bulkQuote _ => 20816
  | .sailRequestForQuoteWithSide _ => 20819
  | .bulkQuoteParticipantBqpProtectionSubscription _ => 21072
  | .requestForQuote _ => 21073
  | .orderCancellation _ => 22597

def encode : FirmMessage → List UInt8
  | .userConnection message => UserConnection.encode message
  | .disconnectionInstruction message => DisconnectionInstruction.encode message
  | .heartbeatResponse message => HeartbeatResponse.encode message
  | .userDisconnection message => UserDisconnection.encode message
  | .orderRequest message => OrderRequest.encode message
  | .bulkQuoteData message => BulkQuoteData.encode message
  | .firmRiskConfig message => FirmRiskConfig.encode message
  | .globalCancellation message => GlobalCancellation.encode message
  | .userGlobalCancellation message => UserGlobalCancellation.encode message
  | .setGroupRiskLimits message => SetGroupRiskLimits.encode message
  | .setGlobalRiskLimits message => SetGlobalRiskLimits.encode message
  | .orderEntry message => OrderEntry.encode message
  | .orderModification message => OrderModification.encode message
  | .newStrategyInstrument message => NewStrategyInstrument.encode message
  | .crossEntry message => CrossEntry.encode message
  | .bulkQuote message => BulkQuote.encode message
  | .sailRequestForQuoteWithSide message => SailRequestForQuoteWithSide.encode message
  | .bulkQuoteParticipantBqpProtectionSubscription message => BulkQuoteParticipantBqpProtectionSubscription.encode message
  | .requestForQuote message => RequestForQuote.encode message
  | .orderCancellation message => OrderCancellation.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : FirmMessage) : (encode message).length ≤ 3996026 := by
  cases message with
  | userConnection inner =>
    have bound_inner := UserConnection.encode_length_le inner
    simp only [encode]
    omega
  | disconnectionInstruction inner =>
    have bound_inner := DisconnectionInstruction.encode_length_le inner
    simp only [encode]
    omega
  | heartbeatResponse inner =>
    simp only [encode, HeartbeatResponse.encode_length]
    omega
  | userDisconnection inner =>
    simp only [encode, UserDisconnection.encode_length]
    omega
  | orderRequest inner =>
    simp only [encode, OrderRequest.encode_length]
    omega
  | bulkQuoteData inner =>
    simp only [encode, BulkQuoteData.encode_length]
    omega
  | firmRiskConfig inner =>
    have bound_inner := FirmRiskConfig.encode_length_le inner
    simp only [encode]
    omega
  | globalCancellation inner =>
    simp only [encode, GlobalCancellation.encode_length]
    omega
  | userGlobalCancellation inner =>
    simp only [encode, UserGlobalCancellation.encode_length]
    omega
  | setGroupRiskLimits inner =>
    have bound_inner := SetGroupRiskLimits.encode_length_le inner
    simp only [encode]
    omega
  | setGlobalRiskLimits inner =>
    simp only [encode, SetGlobalRiskLimits.encode_length]
    omega
  | orderEntry inner =>
    simp only [encode, OrderEntry.encode_length]
    omega
  | orderModification inner =>
    simp only [encode, OrderModification.encode_length]
    omega
  | newStrategyInstrument inner =>
    have bound_inner := NewStrategyInstrument.encode_length_le inner
    simp only [encode]
    omega
  | crossEntry inner =>
    simp only [encode, CrossEntry.encode_length]
    omega
  | bulkQuote inner =>
    have bound_inner := BulkQuote.encode_length_le inner
    simp only [encode]
    omega
  | sailRequestForQuoteWithSide inner =>
    simp only [encode, SailRequestForQuoteWithSide.encode_length]
    omega
  | bulkQuoteParticipantBqpProtectionSubscription inner =>
    simp only [encode, BulkQuoteParticipantBqpProtectionSubscription.encode_length]
    omega
  | requestForQuote inner =>
    simp only [encode, RequestForQuote.encode_length]
    omega
  | orderCancellation inner =>
    simp only [encode, OrderCancellation.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (FirmMessage × List UInt8) :=
  if tag = 21571 then (UserConnection.decode bytes).map fun (message, rest) => (.userConnection message, rest)
  else if tag = 21569 then (DisconnectionInstruction.decode bytes).map fun (message, rest) => (.disconnectionInstruction message, rest)
  else if tag = 21577 then (HeartbeatResponse.decode bytes).map fun (message, rest) => (.heartbeatResponse message, rest)
  else if tag = 21572 then (UserDisconnection.decode bytes).map fun (message, rest) => (.userDisconnection message, rest)
  else if tag = 16710 then (OrderRequest.decode bytes).map fun (message, rest) => (.orderRequest message, rest)
  else if tag = 16964 then (BulkQuoteData.decode bytes).map fun (message, rest) => (.bulkQuoteData message, rest)
  else if tag = 17234 then (FirmRiskConfig.decode bytes).map fun (message, rest) => (.firmRiskConfig message, rest)
  else if tag = 18243 then (GlobalCancellation.decode bytes).map fun (message, rest) => (.globalCancellation message, rest)
  else if tag = 18266 then (UserGlobalCancellation.decode bytes).map fun (message, rest) => (.userGlobalCancellation message, rest)
  else if tag = 19787 then (SetGroupRiskLimits.decode bytes).map fun (message, rest) => (.setGroupRiskLimits message, rest)
  else if tag = 19788 then (SetGlobalRiskLimits.decode bytes).map fun (message, rest) => (.setGlobalRiskLimits message, rest)
  else if tag = 20293 then (OrderEntry.decode bytes).map fun (message, rest) => (.orderEntry message, rest)
  else if tag = 20301 then (OrderModification.decode bytes).map fun (message, rest) => (.orderModification message, rest)
  else if tag = 20302 then (NewStrategyInstrument.decode bytes).map fun (message, rest) => (.newStrategyInstrument message, rest)
  else if tag = 20312 then (CrossEntry.decode bytes).map fun (message, rest) => (.crossEntry message, rest)
  else if tag = 20816 then (BulkQuote.decode bytes).map fun (message, rest) => (.bulkQuote message, rest)
  else if tag = 20819 then (SailRequestForQuoteWithSide.decode bytes).map fun (message, rest) => (.sailRequestForQuoteWithSide message, rest)
  else if tag = 21072 then (BulkQuoteParticipantBqpProtectionSubscription.decode bytes).map fun (message, rest) => (.bulkQuoteParticipantBqpProtectionSubscription message, rest)
  else if tag = 21073 then (RequestForQuote.decode bytes).map fun (message, rest) => (.requestForQuote message, rest)
  else if tag = 22597 then (OrderCancellation.decode bytes).map fun (message, rest) => (.orderCancellation message, rest)
  else none

@[simp] theorem decode_encode (message : FirmMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end FirmMessage

/-- Firm Packet -/
structure FirmPacket where
  messageLength : BitVec 32
  firmMessage : FirmMessage
  endOfText : BitVec 8
  alignmentPadding : Capped 3
  deriving DecidableEq, Repr

namespace FirmPacket

def encode (message : FirmPacket) : List UInt8 :=
  encodeUIntLE 4 message.messageLength
    ++ (encodeUInt 2 (FirmMessage.tag message.firmMessage)
    ++ (FirmMessage.encode message.firmMessage
    ++ (encodeUInt 1 message.endOfText
    ++ (message.alignmentPadding.val))))

def decode (bytes : List UInt8) : Option FirmPacket := do
  let (messageLength, bytes) ← decodeUIntLE 4 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (firmMessage, bytes) ← FirmMessage.decode messageType bytes
  let (endOfText, bytes) ← decodeUInt 1 bytes
  let alignmentPadding_ := bytes
  if fits_alignmentPadding : alignmentPadding_.length ≤ 3 then
    pure { messageLength, firmMessage, endOfText, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
  else none

theorem encode_length_pos (message : FirmPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FirmPacket) : (encode message).length ≤ 3996036 := by
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  cases message.firmMessage with
  | userConnection inner =>
    have bound_inner := UserConnection.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | disconnectionInstruction inner =>
    have bound_inner := DisconnectionInstruction.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | heartbeatResponse inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, HeartbeatResponse.encode_length]
    omega
  | userDisconnection inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, UserDisconnection.encode_length]
    omega
  | orderRequest inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderRequest.encode_length]
    omega
  | bulkQuoteData inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, BulkQuoteData.encode_length]
    omega
  | firmRiskConfig inner =>
    have bound_inner := FirmRiskConfig.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | globalCancellation inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, GlobalCancellation.encode_length]
    omega
  | userGlobalCancellation inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, UserGlobalCancellation.encode_length]
    omega
  | setGroupRiskLimits inner =>
    have bound_inner := SetGroupRiskLimits.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | setGlobalRiskLimits inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SetGlobalRiskLimits.encode_length]
    omega
  | orderEntry inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderEntry.encode_length]
    omega
  | orderModification inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderModification.encode_length]
    omega
  | newStrategyInstrument inner =>
    have bound_inner := NewStrategyInstrument.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | crossEntry inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, CrossEntry.encode_length]
    omega
  | bulkQuote inner =>
    have bound_inner := BulkQuote.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | sailRequestForQuoteWithSide inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SailRequestForQuoteWithSide.encode_length]
    omega
  | bulkQuoteParticipantBqpProtectionSubscription inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, BulkQuoteParticipantBqpProtectionSubscription.encode_length]
    omega
  | requestForQuote inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, RequestForQuote.encode_length]
    omega
  | orderCancellation inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderCancellation.encode_length]
    omega

theorem decode_encode (message : FirmPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [FirmMessage.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.alignmentPadding.length_le]
  rfl

end FirmPacket

end Omi.TmxMxSolaorderentrySailV121Firm
