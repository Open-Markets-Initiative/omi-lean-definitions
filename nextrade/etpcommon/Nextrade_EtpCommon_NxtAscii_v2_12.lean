import Wire

/-!
# Nextrade Nextrade Etp Market Data Common v2.12

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Etp Constituents Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Mm Lp Information Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Equities Batch Data Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Member Information Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Issue Event Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NextradeNextradeEtpcommonNxtasciiV212

/-- Polling Data Message: 5 bytes -/
structure PollingDataMessage where
  currentTime1MinuteInterval : Alpha 4
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace PollingDataMessage

def encode (message : PollingDataMessage) : List UInt8 :=
  Alpha.encode message.currentTime1MinuteInterval
    ++ (Alpha.encode message.endKeyword)

def decode (bytes : List UInt8) : Option (PollingDataMessage × List UInt8) := do
  let (currentTime1MinuteInterval, bytes) ← Alpha.decode 4 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ currentTime1MinuteInterval, endKeyword }, bytes)

@[simp] theorem encode_length (message : PollingDataMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : PollingDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PollingDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PollingDataMessage

/-- Securities Quote Mm Lp Quotes Included 10 Level Message: 825 bytes -/
structure SecuritiesQuoteMmLpQuotesIncluded10LevelMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  askLevel1Price : Alpha 11
  bidLevel1Price : Alpha 11
  askLevel1Volume : Alpha 12
  bidLevel1Volume : Alpha 12
  lpAskLevel1Volume : Alpha 12
  lpBidLevel1Volume : Alpha 12
  askLevel2Price : Alpha 11
  bidLevel2Price : Alpha 11
  askLevel2Volume : Alpha 12
  bidLevel2Volume : Alpha 12
  lpAskLevel2Volume : Alpha 12
  lpBidLevel2Volume : Alpha 12
  askLevel3Price : Alpha 11
  bidLevel3Price : Alpha 11
  askLevel3Volume : Alpha 12
  bidLevel3Volume : Alpha 12
  lpAskLevel3Volume : Alpha 12
  lpBidLevel3Volume : Alpha 12
  askLevel4Price : Alpha 11
  bidLevel4Price : Alpha 11
  askLevel4Volume : Alpha 12
  bidLevel4Volume : Alpha 12
  lpAskLevel4Volume : Alpha 12
  lpBidLevel4Volume : Alpha 12
  askLevel5Price : Alpha 11
  bidLevel5Price : Alpha 11
  askLevel5Volume : Alpha 12
  bidLevel5Volume : Alpha 12
  lpAskLevel5Volume : Alpha 12
  lpBidLevel5Volume : Alpha 12
  askLevel6Price : Alpha 11
  bidLevel6Price : Alpha 11
  askLevel6Volume : Alpha 12
  bidLevel6Volume : Alpha 12
  lpAskLevel6Volume : Alpha 12
  lpBidLevel6Volume : Alpha 12
  askLevel7Price : Alpha 11
  bidLevel7Price : Alpha 11
  askLevel7Volume : Alpha 12
  bidLevel7Volume : Alpha 12
  lpAskLevel7Volume : Alpha 12
  lpBidLevel7Volume : Alpha 12
  askLevel8Price : Alpha 11
  bidLevel8Price : Alpha 11
  askLevel8Volume : Alpha 12
  bidLevel8Volume : Alpha 12
  lpAskLevel8Volume : Alpha 12
  lpBidLevel8Volume : Alpha 12
  askLevel9Price : Alpha 11
  bidLevel9Price : Alpha 11
  askLevel9Volume : Alpha 12
  bidLevel9Volume : Alpha 12
  lpAskLevel9Volume : Alpha 12
  lpBidLevel9Volume : Alpha 12
  askLevel10Price : Alpha 11
  bidLevel10Price : Alpha 11
  askLevel10Volume : Alpha 12
  bidLevel10Volume : Alpha 12
  lpAskLevel10Volume : Alpha 12
  lpBidLevel10Volume : Alpha 12
  totalAskVolume : Alpha 12
  totalBidVolume : Alpha 12
  estimatedTradingPrice : Alpha 11
  estimatedTradingVolume : Alpha 12
  midPrice : Alpha 11
  totalMidPriceAskVolumeTotalAskVolumeOnMidPrice : Alpha 12
  totalMidPriceBidVolumeTotalBidVolumeOnMidPrice : Alpha 12
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace SecuritiesQuoteMmLpQuotesIncluded10LevelMessage

def encode (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.askLevel1Price
    ++ (Alpha.encode message.bidLevel1Price
    ++ (Alpha.encode message.askLevel1Volume
    ++ (Alpha.encode message.bidLevel1Volume
    ++ (Alpha.encode message.lpAskLevel1Volume
    ++ (Alpha.encode message.lpBidLevel1Volume
    ++ (Alpha.encode message.askLevel2Price
    ++ (Alpha.encode message.bidLevel2Price
    ++ (Alpha.encode message.askLevel2Volume
    ++ (Alpha.encode message.bidLevel2Volume
    ++ (Alpha.encode message.lpAskLevel2Volume
    ++ (Alpha.encode message.lpBidLevel2Volume
    ++ (Alpha.encode message.askLevel3Price
    ++ (Alpha.encode message.bidLevel3Price
    ++ (Alpha.encode message.askLevel3Volume
    ++ (Alpha.encode message.bidLevel3Volume
    ++ (Alpha.encode message.lpAskLevel3Volume
    ++ (Alpha.encode message.lpBidLevel3Volume
    ++ (Alpha.encode message.askLevel4Price
    ++ (Alpha.encode message.bidLevel4Price
    ++ (Alpha.encode message.askLevel4Volume
    ++ (Alpha.encode message.bidLevel4Volume
    ++ (Alpha.encode message.lpAskLevel4Volume
    ++ (Alpha.encode message.lpBidLevel4Volume
    ++ (Alpha.encode message.askLevel5Price
    ++ (Alpha.encode message.bidLevel5Price
    ++ (Alpha.encode message.askLevel5Volume
    ++ (Alpha.encode message.bidLevel5Volume
    ++ (Alpha.encode message.lpAskLevel5Volume
    ++ (Alpha.encode message.lpBidLevel5Volume
    ++ (Alpha.encode message.askLevel6Price
    ++ (Alpha.encode message.bidLevel6Price
    ++ (Alpha.encode message.askLevel6Volume
    ++ (Alpha.encode message.bidLevel6Volume
    ++ (Alpha.encode message.lpAskLevel6Volume
    ++ (Alpha.encode message.lpBidLevel6Volume
    ++ (Alpha.encode message.askLevel7Price
    ++ (Alpha.encode message.bidLevel7Price
    ++ (Alpha.encode message.askLevel7Volume
    ++ (Alpha.encode message.bidLevel7Volume
    ++ (Alpha.encode message.lpAskLevel7Volume
    ++ (Alpha.encode message.lpBidLevel7Volume
    ++ (Alpha.encode message.askLevel8Price
    ++ (Alpha.encode message.bidLevel8Price
    ++ (Alpha.encode message.askLevel8Volume
    ++ (Alpha.encode message.bidLevel8Volume
    ++ (Alpha.encode message.lpAskLevel8Volume
    ++ (Alpha.encode message.lpBidLevel8Volume
    ++ (Alpha.encode message.askLevel9Price
    ++ (Alpha.encode message.bidLevel9Price
    ++ (Alpha.encode message.askLevel9Volume
    ++ (Alpha.encode message.bidLevel9Volume
    ++ (Alpha.encode message.lpAskLevel9Volume
    ++ (Alpha.encode message.lpBidLevel9Volume
    ++ (Alpha.encode message.askLevel10Price
    ++ (Alpha.encode message.bidLevel10Price
    ++ (Alpha.encode message.askLevel10Volume
    ++ (Alpha.encode message.bidLevel10Volume
    ++ (Alpha.encode message.lpAskLevel10Volume
    ++ (Alpha.encode message.lpBidLevel10Volume
    ++ (Alpha.encode message.totalAskVolume
    ++ (Alpha.encode message.totalBidVolume
    ++ (Alpha.encode message.estimatedTradingPrice
    ++ (Alpha.encode message.estimatedTradingVolume
    ++ (Alpha.encode message.midPrice
    ++ (Alpha.encode message.totalMidPriceAskVolumeTotalAskVolumeOnMidPrice
    ++ (Alpha.encode message.totalMidPriceBidVolumeTotalBidVolumeOnMidPrice
    ++ (Alpha.encode message.endKeyword)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecuritiesQuoteMmLpQuotesIncluded10LevelMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (askLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel4Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel4Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel5Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel5Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel6Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel6Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel7Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel7Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel8Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel8Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel9Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel9Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel10Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel10Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (totalAskVolume, bytes) ← Alpha.decode 12 bytes
  let (totalBidVolume, bytes) ← Alpha.decode 12 bytes
  let (estimatedTradingPrice, bytes) ← Alpha.decode 11 bytes
  let (estimatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (midPrice, bytes) ← Alpha.decode 11 bytes
  let (totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, askLevel1Price, bidLevel1Price, askLevel1Volume, bidLevel1Volume, lpAskLevel1Volume, lpBidLevel1Volume, askLevel2Price, bidLevel2Price, askLevel2Volume, bidLevel2Volume, lpAskLevel2Volume, lpBidLevel2Volume, askLevel3Price, bidLevel3Price, askLevel3Volume, bidLevel3Volume, lpAskLevel3Volume, lpBidLevel3Volume, askLevel4Price, bidLevel4Price, askLevel4Volume, bidLevel4Volume, lpAskLevel4Volume, lpBidLevel4Volume, askLevel5Price, bidLevel5Price, askLevel5Volume, bidLevel5Volume, lpAskLevel5Volume, lpBidLevel5Volume, askLevel6Price, bidLevel6Price, askLevel6Volume, bidLevel6Volume, lpAskLevel6Volume, lpBidLevel6Volume, askLevel7Price, bidLevel7Price, askLevel7Volume, bidLevel7Volume, lpAskLevel7Volume, lpBidLevel7Volume, askLevel8Price, bidLevel8Price, askLevel8Volume, bidLevel8Volume, lpAskLevel8Volume, lpBidLevel8Volume, askLevel9Price, bidLevel9Price, askLevel9Volume, bidLevel9Volume, lpAskLevel9Volume, lpBidLevel9Volume, askLevel10Price, bidLevel10Price, askLevel10Volume, bidLevel10Volume, lpAskLevel10Volume, lpBidLevel10Volume, totalAskVolume, totalBidVolume, estimatedTradingPrice, estimatedTradingVolume, midPrice, totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, endKeyword }, bytes)

@[simp] theorem encode_length (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) : (encode message).length = 825 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) (rest : List UInt8) :
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

end SecuritiesQuoteMmLpQuotesIncluded10LevelMessage

/-- Securities Order Filled Message: 181 bytes -/
structure SecuritiesOrderFilledMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  priceChangeAgainstPreviousDay : Alpha 1
  aPriceChangeAgainstThePreviousDay : Alpha 11
  tradingPrice : Alpha 11
  tradingVolume : Alpha 10
  openingPrice : Alpha 11
  todaysHigh : Alpha 11
  todaysLow : Alpha 11
  accumulatedTradingVolume : Alpha 12
  accumulatedTradingValue : Alpha 22
  finalAskBidTypeCode : Alpha 1
  lpHoldingQuantity : Alpha 15
  theBestAsk : Alpha 11
  theBestBid : Alpha 11
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace SecuritiesOrderFilledMessage

def encode (message : SecuritiesOrderFilledMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.priceChangeAgainstPreviousDay
    ++ (Alpha.encode message.aPriceChangeAgainstThePreviousDay
    ++ (Alpha.encode message.tradingPrice
    ++ (Alpha.encode message.tradingVolume
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.todaysHigh
    ++ (Alpha.encode message.todaysLow
    ++ (Alpha.encode message.accumulatedTradingVolume
    ++ (Alpha.encode message.accumulatedTradingValue
    ++ (Alpha.encode message.finalAskBidTypeCode
    ++ (Alpha.encode message.lpHoldingQuantity
    ++ (Alpha.encode message.theBestAsk
    ++ (Alpha.encode message.theBestBid
    ++ (Alpha.encode message.endKeyword)))))))))))))))))))

def decode (bytes : List UInt8) : Option (SecuritiesOrderFilledMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (priceChangeAgainstPreviousDay, bytes) ← Alpha.decode 1 bytes
  let (aPriceChangeAgainstThePreviousDay, bytes) ← Alpha.decode 11 bytes
  let (tradingPrice, bytes) ← Alpha.decode 11 bytes
  let (tradingVolume, bytes) ← Alpha.decode 10 bytes
  let (openingPrice, bytes) ← Alpha.decode 11 bytes
  let (todaysHigh, bytes) ← Alpha.decode 11 bytes
  let (todaysLow, bytes) ← Alpha.decode 11 bytes
  let (accumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (finalAskBidTypeCode, bytes) ← Alpha.decode 1 bytes
  let (lpHoldingQuantity, bytes) ← Alpha.decode 15 bytes
  let (theBestAsk, bytes) ← Alpha.decode 11 bytes
  let (theBestBid, bytes) ← Alpha.decode 11 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, priceChangeAgainstPreviousDay, aPriceChangeAgainstThePreviousDay, tradingPrice, tradingVolume, openingPrice, todaysHigh, todaysLow, accumulatedTradingVolume, accumulatedTradingValue, finalAskBidTypeCode, lpHoldingQuantity, theBestAsk, theBestBid, endKeyword }, bytes)

@[simp] theorem encode_length (message : SecuritiesOrderFilledMessage) : (encode message).length = 181 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SecuritiesOrderFilledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecuritiesOrderFilledMessage) (rest : List UInt8) :
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

end SecuritiesOrderFilledMessage

/-- Market Operation Ts Message: 63 bytes -/
structure MarketOperationTsMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  boardEventId : Alpha 3
  startTimeOfABoardEvent : Alpha 9
  boardEventGroupCode : Alpha 5
  tradingHaltReasonCode : Alpha 3
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace MarketOperationTsMessage

def encode (message : MarketOperationTsMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.boardEventId
    ++ (Alpha.encode message.startTimeOfABoardEvent
    ++ (Alpha.encode message.boardEventGroupCode
    ++ (Alpha.encode message.tradingHaltReasonCode
    ++ (Alpha.encode message.endKeyword))))))))))

def decode (bytes : List UInt8) : Option (MarketOperationTsMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (boardEventId, bytes) ← Alpha.decode 3 bytes
  let (startTimeOfABoardEvent, bytes) ← Alpha.decode 9 bytes
  let (boardEventGroupCode, bytes) ← Alpha.decode 5 bytes
  let (tradingHaltReasonCode, bytes) ← Alpha.decode 3 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, boardEventId, startTimeOfABoardEvent, boardEventGroupCode, tradingHaltReasonCode, endKeyword }, bytes)

@[simp] theorem encode_length (message : MarketOperationTsMessage) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MarketOperationTsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketOperationTsMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketOperationTsMessage

/-- Issue Closing Message: 107 bytes -/
structure IssueClosingMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  closingPrice : Alpha 11
  closingPriceTypeCode : Alpha 1
  upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession : Alpha 11
  lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession : Alpha 11
  closingPriceWeightedStockPriceAverage : Alpha 11
  closingPriceBasePriceOfBuyIn : Alpha 11
  closingPriceUpperLimitOfBuyIn : Alpha 11
  closingPriceLowerLimitOfBuyIn : Alpha 11
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace IssueClosingMessage

def encode (message : IssueClosingMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.closingPrice
    ++ (Alpha.encode message.closingPriceTypeCode
    ++ (Alpha.encode message.upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession
    ++ (Alpha.encode message.lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession
    ++ (Alpha.encode message.closingPriceWeightedStockPriceAverage
    ++ (Alpha.encode message.closingPriceBasePriceOfBuyIn
    ++ (Alpha.encode message.closingPriceUpperLimitOfBuyIn
    ++ (Alpha.encode message.closingPriceLowerLimitOfBuyIn
    ++ (Alpha.encode message.endKeyword))))))))))))

def decode (bytes : List UInt8) : Option (IssueClosingMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (closingPrice, bytes) ← Alpha.decode 11 bytes
  let (closingPriceTypeCode, bytes) ← Alpha.decode 1 bytes
  let (upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, bytes) ← Alpha.decode 11 bytes
  let (lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, bytes) ← Alpha.decode 11 bytes
  let (closingPriceWeightedStockPriceAverage, bytes) ← Alpha.decode 11 bytes
  let (closingPriceBasePriceOfBuyIn, bytes) ← Alpha.decode 11 bytes
  let (closingPriceUpperLimitOfBuyIn, bytes) ← Alpha.decode 11 bytes
  let (closingPriceLowerLimitOfBuyIn, bytes) ← Alpha.decode 11 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, closingPrice, closingPriceTypeCode, upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, closingPriceWeightedStockPriceAverage, closingPriceBasePriceOfBuyIn, closingPriceUpperLimitOfBuyIn, closingPriceLowerLimitOfBuyIn, endKeyword }, bytes)

@[simp] theorem encode_length (message : IssueClosingMessage) : (encode message).length = 107 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : IssueClosingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueClosingMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end IssueClosingMessage

/-- Triggering Removing Vi Message: 111 bytes -/
structure TriggeringRemovingViMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  processingTimeOfTradingSystem : Alpha 12
  theTimeEndingVi : Alpha 9
  viStatusCode : Alpha 1
  viTypeCode : Alpha 1
  aBasePriceToTriggerStaticVi : Alpha 11
  aBasePriceToTriggerDynamicVi : Alpha 11
  viTriggeringPrice : Alpha 11
  disparateRatioToTriggerStaticVi : Alpha 13
  disparateRatioToTriggerDynamicVi : Alpha 13
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace TriggeringRemovingViMessage

def encode (message : TriggeringRemovingViMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.theTimeEndingVi
    ++ (Alpha.encode message.viStatusCode
    ++ (Alpha.encode message.viTypeCode
    ++ (Alpha.encode message.aBasePriceToTriggerStaticVi
    ++ (Alpha.encode message.aBasePriceToTriggerDynamicVi
    ++ (Alpha.encode message.viTriggeringPrice
    ++ (Alpha.encode message.disparateRatioToTriggerStaticVi
    ++ (Alpha.encode message.disparateRatioToTriggerDynamicVi
    ++ (Alpha.encode message.endKeyword)))))))))))))

def decode (bytes : List UInt8) : Option (TriggeringRemovingViMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (theTimeEndingVi, bytes) ← Alpha.decode 9 bytes
  let (viStatusCode, bytes) ← Alpha.decode 1 bytes
  let (viTypeCode, bytes) ← Alpha.decode 1 bytes
  let (aBasePriceToTriggerStaticVi, bytes) ← Alpha.decode 11 bytes
  let (aBasePriceToTriggerDynamicVi, bytes) ← Alpha.decode 11 bytes
  let (viTriggeringPrice, bytes) ← Alpha.decode 11 bytes
  let (disparateRatioToTriggerStaticVi, bytes) ← Alpha.decode 13 bytes
  let (disparateRatioToTriggerDynamicVi, bytes) ← Alpha.decode 13 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, theTimeEndingVi, viStatusCode, viTypeCode, aBasePriceToTriggerStaticVi, aBasePriceToTriggerDynamicVi, viTriggeringPrice, disparateRatioToTriggerStaticVi, disparateRatioToTriggerDynamicVi, endKeyword }, bytes)

@[simp] theorem encode_length (message : TriggeringRemovingViMessage) : (encode message).length = 111 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TriggeringRemovingViMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TriggeringRemovingViMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TriggeringRemovingViMessage

/-- Closing Price Trading Quote Message: 53 bytes -/
structure ClosingPriceTradingQuoteMessage where
  messageSequenceNumber : Alpha 8
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  totalAskVolume : Alpha 12
  totalBidVolume : Alpha 12
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace ClosingPriceTradingQuoteMessage

def encode (message : ClosingPriceTradingQuoteMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.totalAskVolume
    ++ (Alpha.encode message.totalBidVolume
    ++ (Alpha.encode message.endKeyword))))))

def decode (bytes : List UInt8) : Option (ClosingPriceTradingQuoteMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (totalAskVolume, bytes) ← Alpha.decode 12 bytes
  let (totalBidVolume, bytes) ← Alpha.decode 12 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, totalAskVolume, totalBidVolume, endKeyword }, bytes)

@[simp] theorem encode_length (message : ClosingPriceTradingQuoteMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ClosingPriceTradingQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClosingPriceTradingQuoteMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClosingPriceTradingQuoteMessage

/-- Equities Snapshot Mm Lp Quotes Included 10 Level Message: 930 bytes -/
structure EquitiesSnapshotMmLpQuotesIncluded10LevelMessage where
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  priceChangeAgainstPreviousDay : Alpha 1
  aPriceChangeAgainstThePreviousDay : Alpha 11
  upperLimitPrice : Alpha 11
  lowerLimitPrice : Alpha 11
  currentPrice : Alpha 11
  openingPrice : Alpha 11
  todaysHigh : Alpha 11
  todaysLow : Alpha 11
  accumulatedTradingVolume : Alpha 12
  accumulatedTradingValue : Alpha 22
  finalAskBidTypeCode : Alpha 1
  askLevel1Price : Alpha 11
  bidLevel1Price : Alpha 11
  askLevel1Volume : Alpha 12
  bidLevel1Volume : Alpha 12
  lpAskLevel1Volume : Alpha 12
  lpBidLevel1Volume : Alpha 12
  askLevel2Price : Alpha 11
  bidLevel2Price : Alpha 11
  askLevel2Volume : Alpha 12
  bidLevel2Volume : Alpha 12
  lpAskLevel2Volume : Alpha 12
  lpBidLevel2Volume : Alpha 12
  askLevel3Price : Alpha 11
  bidLevel3Price : Alpha 11
  askLevel3Volume : Alpha 12
  bidLevel3Volume : Alpha 12
  lpAskLevel3Volume : Alpha 12
  lpBidLevel3Volume : Alpha 12
  askLevel4Price : Alpha 11
  bidLevel4Price : Alpha 11
  askLevel4Volume : Alpha 12
  bidLevel4Volume : Alpha 12
  lpAskLevel4Volume : Alpha 12
  lpBidLevel4Volume : Alpha 12
  askLevel5Price : Alpha 11
  bidLevel5Price : Alpha 11
  askLevel5Volume : Alpha 12
  bidLevel5Volume : Alpha 12
  lpAskLevel5Volume : Alpha 12
  lpBidLevel5Volume : Alpha 12
  askLevel6Price : Alpha 11
  bidLevel6Price : Alpha 11
  askLevel6Volume : Alpha 12
  bidLevel6Volume : Alpha 12
  lpAskLevel6Volume : Alpha 12
  lpBidLevel6Volume : Alpha 12
  askLevel7Price : Alpha 11
  bidLevel7Price : Alpha 11
  askLevel7Volume : Alpha 12
  bidLevel7Volume : Alpha 12
  lpAskLevel7Volume : Alpha 12
  lpBidLevel7Volume : Alpha 12
  askLevel8Price : Alpha 11
  bidLevel8Price : Alpha 11
  askLevel8Volume : Alpha 12
  bidLevel8Volume : Alpha 12
  lpAskLevel8Volume : Alpha 12
  lpBidLevel8Volume : Alpha 12
  askLevel9Price : Alpha 11
  bidLevel9Price : Alpha 11
  askLevel9Volume : Alpha 12
  bidLevel9Volume : Alpha 12
  lpAskLevel9Volume : Alpha 12
  lpBidLevel9Volume : Alpha 12
  askLevel10Price : Alpha 11
  bidLevel10Price : Alpha 11
  askLevel10Volume : Alpha 12
  bidLevel10Volume : Alpha 12
  lpAskLevel10Volume : Alpha 12
  lpBidLevel10Volume : Alpha 12
  totalAskVolume : Alpha 12
  totalBidVolume : Alpha 12
  estimatedTradingPrice : Alpha 11
  estimatedTradingVolume : Alpha 12
  closingPriceTypeCode : Alpha 1
  tradingHalt : Alpha 1
  knockoutElwTypeCode : Alpha 1
  knockoutElwTriggeringTime : Alpha 9
  midPrice : Alpha 11
  totalMidPriceAskVolumeTotalAskVolumeOnMidPrice : Alpha 12
  totalMidPriceBidVolumeTotalBidVolumeOnMidPrice : Alpha 12
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace EquitiesSnapshotMmLpQuotesIncluded10LevelMessage

def encode (message : EquitiesSnapshotMmLpQuotesIncluded10LevelMessage) : List UInt8 :=
  Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.priceChangeAgainstPreviousDay
    ++ (Alpha.encode message.aPriceChangeAgainstThePreviousDay
    ++ (Alpha.encode message.upperLimitPrice
    ++ (Alpha.encode message.lowerLimitPrice
    ++ (Alpha.encode message.currentPrice
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.todaysHigh
    ++ (Alpha.encode message.todaysLow
    ++ (Alpha.encode message.accumulatedTradingVolume
    ++ (Alpha.encode message.accumulatedTradingValue
    ++ (Alpha.encode message.finalAskBidTypeCode
    ++ (Alpha.encode message.askLevel1Price
    ++ (Alpha.encode message.bidLevel1Price
    ++ (Alpha.encode message.askLevel1Volume
    ++ (Alpha.encode message.bidLevel1Volume
    ++ (Alpha.encode message.lpAskLevel1Volume
    ++ (Alpha.encode message.lpBidLevel1Volume
    ++ (Alpha.encode message.askLevel2Price
    ++ (Alpha.encode message.bidLevel2Price
    ++ (Alpha.encode message.askLevel2Volume
    ++ (Alpha.encode message.bidLevel2Volume
    ++ (Alpha.encode message.lpAskLevel2Volume
    ++ (Alpha.encode message.lpBidLevel2Volume
    ++ (Alpha.encode message.askLevel3Price
    ++ (Alpha.encode message.bidLevel3Price
    ++ (Alpha.encode message.askLevel3Volume
    ++ (Alpha.encode message.bidLevel3Volume
    ++ (Alpha.encode message.lpAskLevel3Volume
    ++ (Alpha.encode message.lpBidLevel3Volume
    ++ (Alpha.encode message.askLevel4Price
    ++ (Alpha.encode message.bidLevel4Price
    ++ (Alpha.encode message.askLevel4Volume
    ++ (Alpha.encode message.bidLevel4Volume
    ++ (Alpha.encode message.lpAskLevel4Volume
    ++ (Alpha.encode message.lpBidLevel4Volume
    ++ (Alpha.encode message.askLevel5Price
    ++ (Alpha.encode message.bidLevel5Price
    ++ (Alpha.encode message.askLevel5Volume
    ++ (Alpha.encode message.bidLevel5Volume
    ++ (Alpha.encode message.lpAskLevel5Volume
    ++ (Alpha.encode message.lpBidLevel5Volume
    ++ (Alpha.encode message.askLevel6Price
    ++ (Alpha.encode message.bidLevel6Price
    ++ (Alpha.encode message.askLevel6Volume
    ++ (Alpha.encode message.bidLevel6Volume
    ++ (Alpha.encode message.lpAskLevel6Volume
    ++ (Alpha.encode message.lpBidLevel6Volume
    ++ (Alpha.encode message.askLevel7Price
    ++ (Alpha.encode message.bidLevel7Price
    ++ (Alpha.encode message.askLevel7Volume
    ++ (Alpha.encode message.bidLevel7Volume
    ++ (Alpha.encode message.lpAskLevel7Volume
    ++ (Alpha.encode message.lpBidLevel7Volume
    ++ (Alpha.encode message.askLevel8Price
    ++ (Alpha.encode message.bidLevel8Price
    ++ (Alpha.encode message.askLevel8Volume
    ++ (Alpha.encode message.bidLevel8Volume
    ++ (Alpha.encode message.lpAskLevel8Volume
    ++ (Alpha.encode message.lpBidLevel8Volume
    ++ (Alpha.encode message.askLevel9Price
    ++ (Alpha.encode message.bidLevel9Price
    ++ (Alpha.encode message.askLevel9Volume
    ++ (Alpha.encode message.bidLevel9Volume
    ++ (Alpha.encode message.lpAskLevel9Volume
    ++ (Alpha.encode message.lpBidLevel9Volume
    ++ (Alpha.encode message.askLevel10Price
    ++ (Alpha.encode message.bidLevel10Price
    ++ (Alpha.encode message.askLevel10Volume
    ++ (Alpha.encode message.bidLevel10Volume
    ++ (Alpha.encode message.lpAskLevel10Volume
    ++ (Alpha.encode message.lpBidLevel10Volume
    ++ (Alpha.encode message.totalAskVolume
    ++ (Alpha.encode message.totalBidVolume
    ++ (Alpha.encode message.estimatedTradingPrice
    ++ (Alpha.encode message.estimatedTradingVolume
    ++ (Alpha.encode message.closingPriceTypeCode
    ++ (Alpha.encode message.tradingHalt
    ++ (Alpha.encode message.knockoutElwTypeCode
    ++ (Alpha.encode message.knockoutElwTriggeringTime
    ++ (Alpha.encode message.midPrice
    ++ (Alpha.encode message.totalMidPriceAskVolumeTotalAskVolumeOnMidPrice
    ++ (Alpha.encode message.totalMidPriceBidVolumeTotalBidVolumeOnMidPrice
    ++ (Alpha.encode message.endKeyword))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (EquitiesSnapshotMmLpQuotesIncluded10LevelMessage × List UInt8) := do
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (priceChangeAgainstPreviousDay, bytes) ← Alpha.decode 1 bytes
  let (aPriceChangeAgainstThePreviousDay, bytes) ← Alpha.decode 11 bytes
  let (upperLimitPrice, bytes) ← Alpha.decode 11 bytes
  let (lowerLimitPrice, bytes) ← Alpha.decode 11 bytes
  let (currentPrice, bytes) ← Alpha.decode 11 bytes
  let (openingPrice, bytes) ← Alpha.decode 11 bytes
  let (todaysHigh, bytes) ← Alpha.decode 11 bytes
  let (todaysLow, bytes) ← Alpha.decode 11 bytes
  let (accumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (finalAskBidTypeCode, bytes) ← Alpha.decode 1 bytes
  let (askLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel1Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel1Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel2Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel2Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel3Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel3Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel4Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel4Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel4Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel5Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel5Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel5Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel6Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel6Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel6Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel7Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel7Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel7Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel8Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel8Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel8Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel9Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel9Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel9Volume, bytes) ← Alpha.decode 12 bytes
  let (askLevel10Price, bytes) ← Alpha.decode 11 bytes
  let (bidLevel10Price, bytes) ← Alpha.decode 11 bytes
  let (askLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (bidLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (lpAskLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (lpBidLevel10Volume, bytes) ← Alpha.decode 12 bytes
  let (totalAskVolume, bytes) ← Alpha.decode 12 bytes
  let (totalBidVolume, bytes) ← Alpha.decode 12 bytes
  let (estimatedTradingPrice, bytes) ← Alpha.decode 11 bytes
  let (estimatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (closingPriceTypeCode, bytes) ← Alpha.decode 1 bytes
  let (tradingHalt, bytes) ← Alpha.decode 1 bytes
  let (knockoutElwTypeCode, bytes) ← Alpha.decode 1 bytes
  let (knockoutElwTriggeringTime, bytes) ← Alpha.decode 9 bytes
  let (midPrice, bytes) ← Alpha.decode 11 bytes
  let (totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, bytes) ← Alpha.decode 12 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, priceChangeAgainstPreviousDay, aPriceChangeAgainstThePreviousDay, upperLimitPrice, lowerLimitPrice, currentPrice, openingPrice, todaysHigh, todaysLow, accumulatedTradingVolume, accumulatedTradingValue, finalAskBidTypeCode, askLevel1Price, bidLevel1Price, askLevel1Volume, bidLevel1Volume, lpAskLevel1Volume, lpBidLevel1Volume, askLevel2Price, bidLevel2Price, askLevel2Volume, bidLevel2Volume, lpAskLevel2Volume, lpBidLevel2Volume, askLevel3Price, bidLevel3Price, askLevel3Volume, bidLevel3Volume, lpAskLevel3Volume, lpBidLevel3Volume, askLevel4Price, bidLevel4Price, askLevel4Volume, bidLevel4Volume, lpAskLevel4Volume, lpBidLevel4Volume, askLevel5Price, bidLevel5Price, askLevel5Volume, bidLevel5Volume, lpAskLevel5Volume, lpBidLevel5Volume, askLevel6Price, bidLevel6Price, askLevel6Volume, bidLevel6Volume, lpAskLevel6Volume, lpBidLevel6Volume, askLevel7Price, bidLevel7Price, askLevel7Volume, bidLevel7Volume, lpAskLevel7Volume, lpBidLevel7Volume, askLevel8Price, bidLevel8Price, askLevel8Volume, bidLevel8Volume, lpAskLevel8Volume, lpBidLevel8Volume, askLevel9Price, bidLevel9Price, askLevel9Volume, bidLevel9Volume, lpAskLevel9Volume, lpBidLevel9Volume, askLevel10Price, bidLevel10Price, askLevel10Volume, bidLevel10Volume, lpAskLevel10Volume, lpBidLevel10Volume, totalAskVolume, totalBidVolume, estimatedTradingPrice, estimatedTradingVolume, closingPriceTypeCode, tradingHalt, knockoutElwTypeCode, knockoutElwTriggeringTime, midPrice, totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, endKeyword }, bytes)

@[simp] theorem encode_length (message : EquitiesSnapshotMmLpQuotesIncluded10LevelMessage) : (encode message).length = 930 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EquitiesSnapshotMmLpQuotesIncluded10LevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : EquitiesSnapshotMmLpQuotesIncluded10LevelMessage) (rest : List UInt8) :
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

end EquitiesSnapshotMmLpQuotesIncluded10LevelMessage

/-- Investor Activities Per Commodities Message: 79 bytes -/
structure InvestorActivitiesPerCommoditiesMessage where
  calculationTime : Alpha 6
  investorCode : Alpha 4
  accumulatedAskTradingVolume : Alpha 12
  accumulatedAskTradingValue : Alpha 22
  accumulatedBidTradingVolume : Alpha 12
  accumulatedBidTradingValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace InvestorActivitiesPerCommoditiesMessage

def encode (message : InvestorActivitiesPerCommoditiesMessage) : List UInt8 :=
  Alpha.encode message.calculationTime
    ++ (Alpha.encode message.investorCode
    ++ (Alpha.encode message.accumulatedAskTradingVolume
    ++ (Alpha.encode message.accumulatedAskTradingValue
    ++ (Alpha.encode message.accumulatedBidTradingVolume
    ++ (Alpha.encode message.accumulatedBidTradingValue
    ++ (Alpha.encode message.endKeyword))))))

def decode (bytes : List UInt8) : Option (InvestorActivitiesPerCommoditiesMessage × List UInt8) := do
  let (calculationTime, bytes) ← Alpha.decode 6 bytes
  let (investorCode, bytes) ← Alpha.decode 4 bytes
  let (accumulatedAskTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedAskTradingValue, bytes) ← Alpha.decode 22 bytes
  let (accumulatedBidTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedBidTradingValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ calculationTime, investorCode, accumulatedAskTradingVolume, accumulatedAskTradingValue, accumulatedBidTradingVolume, accumulatedBidTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : InvestorActivitiesPerCommoditiesMessage) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : InvestorActivitiesPerCommoditiesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InvestorActivitiesPerCommoditiesMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end InvestorActivitiesPerCommoditiesMessage

/-- Etp Constituents Message: 204 bytes -/
structure EtpConstituentsMessage where
  messageSequenceNumber : Alpha 8
  indexCalculationInstitutionTypeCode : Alpha 2
  indexMarketClassificationId : Alpha 6
  indexSequenceNumber : Alpha 3
  indexLeverageInverseTypeCode : Alpha 2
  indexName : Alpha 80
  indexNameInEn : Alpha 80
  indexAssetClassificationId1 : Alpha 6
  indexAssetClassificationId2 : Alpha 6
  indexId : Alpha 6
  filler4 : Alpha 4
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace EtpConstituentsMessage

def encode (message : EtpConstituentsMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.indexCalculationInstitutionTypeCode
    ++ (Alpha.encode message.indexMarketClassificationId
    ++ (Alpha.encode message.indexSequenceNumber
    ++ (Alpha.encode message.indexLeverageInverseTypeCode
    ++ (Alpha.encode message.indexName
    ++ (Alpha.encode message.indexNameInEn
    ++ (Alpha.encode message.indexAssetClassificationId1
    ++ (Alpha.encode message.indexAssetClassificationId2
    ++ (Alpha.encode message.indexId
    ++ (Alpha.encode message.filler4
    ++ (Alpha.encode message.endKeyword)))))))))))

def decode (bytes : List UInt8) : Option (EtpConstituentsMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (indexCalculationInstitutionTypeCode, bytes) ← Alpha.decode 2 bytes
  let (indexMarketClassificationId, bytes) ← Alpha.decode 6 bytes
  let (indexSequenceNumber, bytes) ← Alpha.decode 3 bytes
  let (indexLeverageInverseTypeCode, bytes) ← Alpha.decode 2 bytes
  let (indexName, bytes) ← Alpha.decode 80 bytes
  let (indexNameInEn, bytes) ← Alpha.decode 80 bytes
  let (indexAssetClassificationId1, bytes) ← Alpha.decode 6 bytes
  let (indexAssetClassificationId2, bytes) ← Alpha.decode 6 bytes
  let (indexId, bytes) ← Alpha.decode 6 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, indexCalculationInstitutionTypeCode, indexMarketClassificationId, indexSequenceNumber, indexLeverageInverseTypeCode, indexName, indexNameInEn, indexAssetClassificationId1, indexAssetClassificationId2, indexId, filler4, endKeyword }, bytes)

@[simp] theorem encode_length (message : EtpConstituentsMessage) : (encode message).length = 204 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EtpConstituentsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EtpConstituentsMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end EtpConstituentsMessage

/-- Mm Lp Information Message: 217 bytes -/
structure MmLpInformationMessage where
  messageSequenceNumber : Alpha 8
  isinCode : Alpha 12
  marketParticipantNumber : Alpha 5
  boardId : Alpha 2
  marketMakingLpTypeCode : Alpha 1
  lpStartDate : Alpha 8
  lpEndDate : Alpha 8
  minimumOrderVolume : Alpha 11
  maximumVolumeOfMultipleOrder : Alpha 11
  bidAskSpreadUnitCode : Alpha 1
  mainMarketBidAskSpreadValue : Alpha 22
  spreadMultipleForMarketHolidays : Alpha 11
  anObligatoryTimeIntervalToPlaceAnOrder : Alpha 6
  minimumAskPrice : Alpha 22
  maximumBidPrice : Alpha 22
  minimumOrderPrice : Alpha 22
  maximumOrderPrice : Alpha 22
  extendedMarketBidAskSpreadValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace MmLpInformationMessage

def encode (message : MmLpInformationMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.marketParticipantNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.marketMakingLpTypeCode
    ++ (Alpha.encode message.lpStartDate
    ++ (Alpha.encode message.lpEndDate
    ++ (Alpha.encode message.minimumOrderVolume
    ++ (Alpha.encode message.maximumVolumeOfMultipleOrder
    ++ (Alpha.encode message.bidAskSpreadUnitCode
    ++ (Alpha.encode message.mainMarketBidAskSpreadValue
    ++ (Alpha.encode message.spreadMultipleForMarketHolidays
    ++ (Alpha.encode message.anObligatoryTimeIntervalToPlaceAnOrder
    ++ (Alpha.encode message.minimumAskPrice
    ++ (Alpha.encode message.maximumBidPrice
    ++ (Alpha.encode message.minimumOrderPrice
    ++ (Alpha.encode message.maximumOrderPrice
    ++ (Alpha.encode message.extendedMarketBidAskSpreadValue
    ++ (Alpha.encode message.endKeyword))))))))))))))))))

def decode (bytes : List UInt8) : Option (MmLpInformationMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (marketParticipantNumber, bytes) ← Alpha.decode 5 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (marketMakingLpTypeCode, bytes) ← Alpha.decode 1 bytes
  let (lpStartDate, bytes) ← Alpha.decode 8 bytes
  let (lpEndDate, bytes) ← Alpha.decode 8 bytes
  let (minimumOrderVolume, bytes) ← Alpha.decode 11 bytes
  let (maximumVolumeOfMultipleOrder, bytes) ← Alpha.decode 11 bytes
  let (bidAskSpreadUnitCode, bytes) ← Alpha.decode 1 bytes
  let (mainMarketBidAskSpreadValue, bytes) ← Alpha.decode 22 bytes
  let (spreadMultipleForMarketHolidays, bytes) ← Alpha.decode 11 bytes
  let (anObligatoryTimeIntervalToPlaceAnOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumAskPrice, bytes) ← Alpha.decode 22 bytes
  let (maximumBidPrice, bytes) ← Alpha.decode 22 bytes
  let (minimumOrderPrice, bytes) ← Alpha.decode 22 bytes
  let (maximumOrderPrice, bytes) ← Alpha.decode 22 bytes
  let (extendedMarketBidAskSpreadValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, isinCode, marketParticipantNumber, boardId, marketMakingLpTypeCode, lpStartDate, lpEndDate, minimumOrderVolume, maximumVolumeOfMultipleOrder, bidAskSpreadUnitCode, mainMarketBidAskSpreadValue, spreadMultipleForMarketHolidays, anObligatoryTimeIntervalToPlaceAnOrder, minimumAskPrice, maximumBidPrice, minimumOrderPrice, maximumOrderPrice, extendedMarketBidAskSpreadValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : MmLpInformationMessage) : (encode message).length = 217 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MmLpInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MmLpInformationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MmLpInformationMessage

/-- Market Operation Schedule Message: 78 bytes -/
structure MarketOperationScheduleMessage where
  marketOperationProductId : Alpha 3
  boardId : Alpha 2
  boardEventId : Alpha 3
  startTimeOfABoardEvent : Alpha 9
  boardEventGroupCode : Alpha 5
  sessionStartEndCode : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  isinCodeOfACommonStock : Alpha 12
  productId : Alpha 11
  tradingHaltReasonCode : Alpha 3
  tradingHaltTypeCode : Alpha 1
  stepApplied : Alpha 2
  priceLimitRangeExpansionForBaseIssueTypeCode : Alpha 1
  expectedTimeOfExpandingPriceLimitRange : Alpha 9
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace MarketOperationScheduleMessage

def encode (message : MarketOperationScheduleMessage) : List UInt8 :=
  Alpha.encode message.marketOperationProductId
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.boardEventId
    ++ (Alpha.encode message.startTimeOfABoardEvent
    ++ (Alpha.encode message.boardEventGroupCode
    ++ (Alpha.encode message.sessionStartEndCode
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.isinCodeOfACommonStock
    ++ (Alpha.encode message.productId
    ++ (Alpha.encode message.tradingHaltReasonCode
    ++ (Alpha.encode message.tradingHaltTypeCode
    ++ (Alpha.encode message.stepApplied
    ++ (Alpha.encode message.priceLimitRangeExpansionForBaseIssueTypeCode
    ++ (Alpha.encode message.expectedTimeOfExpandingPriceLimitRange
    ++ (Alpha.encode message.endKeyword)))))))))))))))

def decode (bytes : List UInt8) : Option (MarketOperationScheduleMessage × List UInt8) := do
  let (marketOperationProductId, bytes) ← Alpha.decode 3 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (boardEventId, bytes) ← Alpha.decode 3 bytes
  let (startTimeOfABoardEvent, bytes) ← Alpha.decode 9 bytes
  let (boardEventGroupCode, bytes) ← Alpha.decode 5 bytes
  let (sessionStartEndCode, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (isinCodeOfACommonStock, bytes) ← Alpha.decode 12 bytes
  let (productId, bytes) ← Alpha.decode 11 bytes
  let (tradingHaltReasonCode, bytes) ← Alpha.decode 3 bytes
  let (tradingHaltTypeCode, bytes) ← Alpha.decode 1 bytes
  let (stepApplied, bytes) ← Alpha.decode 2 bytes
  let (priceLimitRangeExpansionForBaseIssueTypeCode, bytes) ← Alpha.decode 1 bytes
  let (expectedTimeOfExpandingPriceLimitRange, bytes) ← Alpha.decode 9 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ marketOperationProductId, boardId, boardEventId, startTimeOfABoardEvent, boardEventGroupCode, sessionStartEndCode, sessionId, isinCode, isinCodeOfACommonStock, productId, tradingHaltReasonCode, tradingHaltTypeCode, stepApplied, priceLimitRangeExpansionForBaseIssueTypeCode, expectedTimeOfExpandingPriceLimitRange, endKeyword }, bytes)

@[simp] theorem encode_length (message : MarketOperationScheduleMessage) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MarketOperationScheduleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketOperationScheduleMessage) (rest : List UInt8) :
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

end MarketOperationScheduleMessage

/-- Member Firm Imposing Lifting Sanctions Message: 41 bytes -/
structure MemberFirmImposingLiftingSanctionsMessage where
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  disclosingDataTypeCode : Alpha 3
  disclosureTime : Alpha 9
  memberNumber : Alpha 5
  memberFirmTrustPrincipalTypeCode : Alpha 5
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace MemberFirmImposingLiftingSanctionsMessage

def encode (message : MemberFirmImposingLiftingSanctionsMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.disclosingDataTypeCode
    ++ (Alpha.encode message.disclosureTime
    ++ (Alpha.encode message.memberNumber
    ++ (Alpha.encode message.memberFirmTrustPrincipalTypeCode
    ++ (Alpha.encode message.endKeyword))))))

def decode (bytes : List UInt8) : Option (MemberFirmImposingLiftingSanctionsMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (disclosingDataTypeCode, bytes) ← Alpha.decode 3 bytes
  let (disclosureTime, bytes) ← Alpha.decode 9 bytes
  let (memberNumber, bytes) ← Alpha.decode 5 bytes
  let (memberFirmTrustPrincipalTypeCode, bytes) ← Alpha.decode 5 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ isinCode, aDesignatedNumberForAnIssueFromKrx, disclosingDataTypeCode, disclosureTime, memberNumber, memberFirmTrustPrincipalTypeCode, endKeyword }, bytes)

@[simp] theorem encode_length (message : MemberFirmImposingLiftingSanctionsMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MemberFirmImposingLiftingSanctionsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MemberFirmImposingLiftingSanctionsMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end MemberFirmImposingLiftingSanctionsMessage

/-- Top Five Traders Activities Message: 409 bytes -/
structure TopFiveTradersActivitiesMessage where
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  memberNumber1ForAsk : Alpha 5
  askTradingVolume1 : Alpha 12
  askTradingValue1 : Alpha 22
  memberNumber1ForBid : Alpha 5
  bidTradingVolume1 : Alpha 12
  bidTradingValue1 : Alpha 22
  memberNumber2ForAsk : Alpha 5
  askTradingVolume2 : Alpha 12
  askTradingValue2 : Alpha 22
  memberNumber2ForBid : Alpha 5
  bidTradingVolume2 : Alpha 12
  bidTradingValue2 : Alpha 22
  memberNumber3ForAsk : Alpha 5
  askTradingVolume3 : Alpha 12
  askTradingValue3 : Alpha 22
  memberNumber3ForBid : Alpha 5
  bidTradingVolume3 : Alpha 12
  bidTradingValue3 : Alpha 22
  memberNumber4ForAsk : Alpha 5
  askTradingVolume4 : Alpha 12
  askTradingValue4 : Alpha 22
  memberNumber4ForBid : Alpha 5
  bidTradingVolume4 : Alpha 12
  bidTradingValue4 : Alpha 22
  memberNumber5ForAsk : Alpha 5
  askTradingVolume5 : Alpha 12
  askTradingValue5 : Alpha 22
  memberNumber5ForBid : Alpha 5
  bidTradingVolume5 : Alpha 12
  bidTradingValue5 : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace TopFiveTradersActivitiesMessage

def encode (message : TopFiveTradersActivitiesMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.memberNumber1ForAsk
    ++ (Alpha.encode message.askTradingVolume1
    ++ (Alpha.encode message.askTradingValue1
    ++ (Alpha.encode message.memberNumber1ForBid
    ++ (Alpha.encode message.bidTradingVolume1
    ++ (Alpha.encode message.bidTradingValue1
    ++ (Alpha.encode message.memberNumber2ForAsk
    ++ (Alpha.encode message.askTradingVolume2
    ++ (Alpha.encode message.askTradingValue2
    ++ (Alpha.encode message.memberNumber2ForBid
    ++ (Alpha.encode message.bidTradingVolume2
    ++ (Alpha.encode message.bidTradingValue2
    ++ (Alpha.encode message.memberNumber3ForAsk
    ++ (Alpha.encode message.askTradingVolume3
    ++ (Alpha.encode message.askTradingValue3
    ++ (Alpha.encode message.memberNumber3ForBid
    ++ (Alpha.encode message.bidTradingVolume3
    ++ (Alpha.encode message.bidTradingValue3
    ++ (Alpha.encode message.memberNumber4ForAsk
    ++ (Alpha.encode message.askTradingVolume4
    ++ (Alpha.encode message.askTradingValue4
    ++ (Alpha.encode message.memberNumber4ForBid
    ++ (Alpha.encode message.bidTradingVolume4
    ++ (Alpha.encode message.bidTradingValue4
    ++ (Alpha.encode message.memberNumber5ForAsk
    ++ (Alpha.encode message.askTradingVolume5
    ++ (Alpha.encode message.askTradingValue5
    ++ (Alpha.encode message.memberNumber5ForBid
    ++ (Alpha.encode message.bidTradingVolume5
    ++ (Alpha.encode message.bidTradingValue5
    ++ (Alpha.encode message.endKeyword))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TopFiveTradersActivitiesMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (memberNumber1ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume1, bytes) ← Alpha.decode 12 bytes
  let (askTradingValue1, bytes) ← Alpha.decode 22 bytes
  let (memberNumber1ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume1, bytes) ← Alpha.decode 12 bytes
  let (bidTradingValue1, bytes) ← Alpha.decode 22 bytes
  let (memberNumber2ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume2, bytes) ← Alpha.decode 12 bytes
  let (askTradingValue2, bytes) ← Alpha.decode 22 bytes
  let (memberNumber2ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume2, bytes) ← Alpha.decode 12 bytes
  let (bidTradingValue2, bytes) ← Alpha.decode 22 bytes
  let (memberNumber3ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume3, bytes) ← Alpha.decode 12 bytes
  let (askTradingValue3, bytes) ← Alpha.decode 22 bytes
  let (memberNumber3ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume3, bytes) ← Alpha.decode 12 bytes
  let (bidTradingValue3, bytes) ← Alpha.decode 22 bytes
  let (memberNumber4ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume4, bytes) ← Alpha.decode 12 bytes
  let (askTradingValue4, bytes) ← Alpha.decode 22 bytes
  let (memberNumber4ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume4, bytes) ← Alpha.decode 12 bytes
  let (bidTradingValue4, bytes) ← Alpha.decode 22 bytes
  let (memberNumber5ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume5, bytes) ← Alpha.decode 12 bytes
  let (askTradingValue5, bytes) ← Alpha.decode 22 bytes
  let (memberNumber5ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume5, bytes) ← Alpha.decode 12 bytes
  let (bidTradingValue5, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ isinCode, aDesignatedNumberForAnIssueFromKrx, memberNumber1ForAsk, askTradingVolume1, askTradingValue1, memberNumber1ForBid, bidTradingVolume1, bidTradingValue1, memberNumber2ForAsk, askTradingVolume2, askTradingValue2, memberNumber2ForBid, bidTradingVolume2, bidTradingValue2, memberNumber3ForAsk, askTradingVolume3, askTradingValue3, memberNumber3ForBid, bidTradingVolume3, bidTradingValue3, memberNumber4ForAsk, askTradingVolume4, askTradingValue4, memberNumber4ForBid, bidTradingVolume4, bidTradingValue4, memberNumber5ForAsk, askTradingVolume5, askTradingValue5, memberNumber5ForBid, bidTradingVolume5, bidTradingValue5, endKeyword }, bytes)

@[simp] theorem encode_length (message : TopFiveTradersActivitiesMessage) : (encode message).length = 409 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TopFiveTradersActivitiesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TopFiveTradersActivitiesMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TopFiveTradersActivitiesMessage

/-- Equities Batch Data Message: 649 bytes -/
structure EquitiesBatchDataMessage where
  messageSequenceNumber : Alpha 8
  totalNumberOfInstrumentsOfTheContract : Alpha 6
  businessDate : Alpha 8
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  abbreviatedIssueCode : Alpha 9
  abbreviatedIssueName : Alpha 40
  abbreviatedIssueNameInEn : Alpha 40
  groupNumber : Alpha 5
  marketOperationProductId : Alpha 3
  securityGroupId : Alpha 2
  unitTrading : Alpha 1
  rightsTypeCode : Alpha 2
  parValueTypeCode : Alpha 2
  anIssueOfWhichBasePriceIsSettledWithATodaysSinglePrice : Alpha 1
  reevaluationReasonCode : Alpha 2
  basePriceChange : Alpha 1
  randomEndTriggerCode : Alpha 1
  marketAlert : Alpha 1
  marketAlertTypeCode : Alpha 2
  koreaCorporateGovernanceStockPriceIndexKogi : Alpha 1
  issueForAdministration : Alpha 1
  unfaithfulDisclosure : Alpha 1
  backdoorListing : Alpha 1
  tradingHalt : Alpha 1
  industryId : Alpha 10
  smallMediumSizedBusiness : Alpha 1
  sectionTypeCode : Alpha 1
  investmentInstitutionTypeCode : Alpha 1
  basePrice : Alpha 11
  yesterdaysClosingPriceTypeCodeKrx : Alpha 1
  yesterdaysClosingPriceKrx : Alpha 11
  yesterdaysAccumulatedTradingAmount : Alpha 12
  yesterdaysAccumulatedTradingValue : Alpha 22
  upperLimitPrice : Alpha 11
  lowerLimitPrice : Alpha 11
  substitutePriceOfSecurities : Alpha 11
  parValue : Alpha 11
  issuingPrice : Alpha 11
  listingDate : Alpha 8
  numberOfListedShares : Alpha 16
  liquidationTrade : Alpha 1
  theEstablishmentDate : Alpha 8
  maturityDate : Alpha 8
  exercisingPeriod : Alpha 8
  expirationDateForRight : Alpha 8
  exercisePriceOfElwOrBw : Alpha 13
  capital : Alpha 22
  creditOrderPossibility : Alpha 1
  limitOrderPermissionTypeCode : Alpha 5
  marketPriceOrderPermissionTypeCode : Alpha 5
  conditionedOrderPermissionTypeCode : Alpha 5
  bestFavorableOrderPermissionTypeCode : Alpha 5
  firstBestOrderPermissionType : Alpha 5
  midPriceOrderPermissionTypeCode : Alpha 5
  stopLimitPriceOrderPermissionTypeCode : Alpha 5
  capitalIncreaseTypeCode : Alpha 2
  otherStockTypeCode : Alpha 1
  nationalStock : Alpha 1
  appraisedPrice : Alpha 11
  lowestOrderPrice : Alpha 11
  highestOrderPrice : Alpha 11
  unitOfVolumeInMainBoard : Alpha 11
  lotSizeAfterhoursTrading : Alpha 11
  reiTsTypeCode : Alpha 1
  targetStockIsinCode : Alpha 12
  currencyIsoCode : Alpha 3
  countryCode : Alpha 3
  marketMakingPossibility : Alpha 1
  closingPriceTradingPossibilityInTheAfterHours : Alpha 1
  closingPriceTradingInThePreopeningMarket : Alpha 1
  blockTradingInThePreopeningMarket : Alpha 1
  basketTradingInThePreopeningMarket : Alpha 1
  announcementOfEstimatedTradingPrice : Alpha 1
  shortSelling : Alpha 1
  etfTrackingDifference : Alpha 13
  regs : Alpha 1
  spac : Alpha 1
  taxTypeCode : Alpha 1
  appraisalRatioOfSubstitutePrice : Alpha 13
  investmentCautionIssue : Alpha 1
  delistingDate : Alpha 8
  shorttermOverheatIssueTypeCode : Alpha 1
  etfReplicationMethodsTypeCode : Alpha 1
  expirationDate : Alpha 8
  distributionTypeCode : Alpha 2
  calculationOfRedemptionPriceStartDate : Alpha 8
  calculationOfRedemptionPriceEndDate : Alpha 8
  etpProductTypeCode : Alpha 1
  indexCalculationInstitutionTypeCode : Alpha 2
  indexMarketClassificationId : Alpha 6
  indexSequenceNumber : Alpha 3
  trackingIndexLeverageInverseTypeCode : Alpha 2
  referenceIndexLeverageInverseTypeCode : Alpha 2
  indexAssetClassificationId1 : Alpha 6
  indexAssetClassificationId2 : Alpha 6
  ipoUnderwriterMemberNumber : Alpha 5
  lpOrder : Alpha 1
  lowLiquidity : Alpha 1
  abnormalRise : Alpha 1
  upperLimitQuantity : Alpha 23
  investmentPrecautionIssue : Alpha 1
  preferredStocksWithLesserShares : Alpha 1
  spacMerger : Alpha 1
  segmentTypeCode : Alpha 1
  afterMarketPossibility : Alpha 1
  choiceOnCompetitiveTrading : Alpha 1
  limitOnCompetitiveTradingVolume : Alpha 1
  occurrenceOfReasonsProhibitingCompetitiveTrading : Alpha 1
  approvalOnCompetitiveTrading : Alpha 1
  approvalOnNegotiationTrading : Alpha 1
  yesterdaysClosingPriceTypeCodeNxt : Alpha 1
  yesterdaysClosingPriceNxt : Alpha 11
  competitionBoardTradePermissionCode : Alpha 5
  negotiationPossibleOrNotBeforeMainMarket : Alpha 1
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace EquitiesBatchDataMessage

def encode (message : EquitiesBatchDataMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.totalNumberOfInstrumentsOfTheContract
    ++ (Alpha.encode message.businessDate
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.abbreviatedIssueCode
    ++ (Alpha.encode message.abbreviatedIssueName
    ++ (Alpha.encode message.abbreviatedIssueNameInEn
    ++ (Alpha.encode message.groupNumber
    ++ (Alpha.encode message.marketOperationProductId
    ++ (Alpha.encode message.securityGroupId
    ++ (Alpha.encode message.unitTrading
    ++ (Alpha.encode message.rightsTypeCode
    ++ (Alpha.encode message.parValueTypeCode
    ++ (Alpha.encode message.anIssueOfWhichBasePriceIsSettledWithATodaysSinglePrice
    ++ (Alpha.encode message.reevaluationReasonCode
    ++ (Alpha.encode message.basePriceChange
    ++ (Alpha.encode message.randomEndTriggerCode
    ++ (Alpha.encode message.marketAlert
    ++ (Alpha.encode message.marketAlertTypeCode
    ++ (Alpha.encode message.koreaCorporateGovernanceStockPriceIndexKogi
    ++ (Alpha.encode message.issueForAdministration
    ++ (Alpha.encode message.unfaithfulDisclosure
    ++ (Alpha.encode message.backdoorListing
    ++ (Alpha.encode message.tradingHalt
    ++ (Alpha.encode message.industryId
    ++ (Alpha.encode message.smallMediumSizedBusiness
    ++ (Alpha.encode message.sectionTypeCode
    ++ (Alpha.encode message.investmentInstitutionTypeCode
    ++ (Alpha.encode message.basePrice
    ++ (Alpha.encode message.yesterdaysClosingPriceTypeCodeKrx
    ++ (Alpha.encode message.yesterdaysClosingPriceKrx
    ++ (Alpha.encode message.yesterdaysAccumulatedTradingAmount
    ++ (Alpha.encode message.yesterdaysAccumulatedTradingValue
    ++ (Alpha.encode message.upperLimitPrice
    ++ (Alpha.encode message.lowerLimitPrice
    ++ (Alpha.encode message.substitutePriceOfSecurities
    ++ (Alpha.encode message.parValue
    ++ (Alpha.encode message.issuingPrice
    ++ (Alpha.encode message.listingDate
    ++ (Alpha.encode message.numberOfListedShares
    ++ (Alpha.encode message.liquidationTrade
    ++ (Alpha.encode message.theEstablishmentDate
    ++ (Alpha.encode message.maturityDate
    ++ (Alpha.encode message.exercisingPeriod
    ++ (Alpha.encode message.expirationDateForRight
    ++ (Alpha.encode message.exercisePriceOfElwOrBw
    ++ (Alpha.encode message.capital
    ++ (Alpha.encode message.creditOrderPossibility
    ++ (Alpha.encode message.limitOrderPermissionTypeCode
    ++ (Alpha.encode message.marketPriceOrderPermissionTypeCode
    ++ (Alpha.encode message.conditionedOrderPermissionTypeCode
    ++ (Alpha.encode message.bestFavorableOrderPermissionTypeCode
    ++ (Alpha.encode message.firstBestOrderPermissionType
    ++ (Alpha.encode message.midPriceOrderPermissionTypeCode
    ++ (Alpha.encode message.stopLimitPriceOrderPermissionTypeCode
    ++ (Alpha.encode message.capitalIncreaseTypeCode
    ++ (Alpha.encode message.otherStockTypeCode
    ++ (Alpha.encode message.nationalStock
    ++ (Alpha.encode message.appraisedPrice
    ++ (Alpha.encode message.lowestOrderPrice
    ++ (Alpha.encode message.highestOrderPrice
    ++ (Alpha.encode message.unitOfVolumeInMainBoard
    ++ (Alpha.encode message.lotSizeAfterhoursTrading
    ++ (Alpha.encode message.reiTsTypeCode
    ++ (Alpha.encode message.targetStockIsinCode
    ++ (Alpha.encode message.currencyIsoCode
    ++ (Alpha.encode message.countryCode
    ++ (Alpha.encode message.marketMakingPossibility
    ++ (Alpha.encode message.closingPriceTradingPossibilityInTheAfterHours
    ++ (Alpha.encode message.closingPriceTradingInThePreopeningMarket
    ++ (Alpha.encode message.blockTradingInThePreopeningMarket
    ++ (Alpha.encode message.basketTradingInThePreopeningMarket
    ++ (Alpha.encode message.announcementOfEstimatedTradingPrice
    ++ (Alpha.encode message.shortSelling
    ++ (Alpha.encode message.etfTrackingDifference
    ++ (Alpha.encode message.regs
    ++ (Alpha.encode message.spac
    ++ (Alpha.encode message.taxTypeCode
    ++ (Alpha.encode message.appraisalRatioOfSubstitutePrice
    ++ (Alpha.encode message.investmentCautionIssue
    ++ (Alpha.encode message.delistingDate
    ++ (Alpha.encode message.shorttermOverheatIssueTypeCode
    ++ (Alpha.encode message.etfReplicationMethodsTypeCode
    ++ (Alpha.encode message.expirationDate
    ++ (Alpha.encode message.distributionTypeCode
    ++ (Alpha.encode message.calculationOfRedemptionPriceStartDate
    ++ (Alpha.encode message.calculationOfRedemptionPriceEndDate
    ++ (Alpha.encode message.etpProductTypeCode
    ++ (Alpha.encode message.indexCalculationInstitutionTypeCode
    ++ (Alpha.encode message.indexMarketClassificationId
    ++ (Alpha.encode message.indexSequenceNumber
    ++ (Alpha.encode message.trackingIndexLeverageInverseTypeCode
    ++ (Alpha.encode message.referenceIndexLeverageInverseTypeCode
    ++ (Alpha.encode message.indexAssetClassificationId1
    ++ (Alpha.encode message.indexAssetClassificationId2
    ++ (Alpha.encode message.ipoUnderwriterMemberNumber
    ++ (Alpha.encode message.lpOrder
    ++ (Alpha.encode message.lowLiquidity
    ++ (Alpha.encode message.abnormalRise
    ++ (Alpha.encode message.upperLimitQuantity
    ++ (Alpha.encode message.investmentPrecautionIssue
    ++ (Alpha.encode message.preferredStocksWithLesserShares
    ++ (Alpha.encode message.spacMerger
    ++ (Alpha.encode message.segmentTypeCode
    ++ (Alpha.encode message.afterMarketPossibility
    ++ (Alpha.encode message.choiceOnCompetitiveTrading
    ++ (Alpha.encode message.limitOnCompetitiveTradingVolume
    ++ (Alpha.encode message.occurrenceOfReasonsProhibitingCompetitiveTrading
    ++ (Alpha.encode message.approvalOnCompetitiveTrading
    ++ (Alpha.encode message.approvalOnNegotiationTrading
    ++ (Alpha.encode message.yesterdaysClosingPriceTypeCodeNxt
    ++ (Alpha.encode message.yesterdaysClosingPriceNxt
    ++ (Alpha.encode message.competitionBoardTradePermissionCode
    ++ (Alpha.encode message.negotiationPossibleOrNotBeforeMainMarket
    ++ (Alpha.encode message.endKeyword)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (EquitiesBatchDataMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (totalNumberOfInstrumentsOfTheContract, bytes) ← Alpha.decode 6 bytes
  let (businessDate, bytes) ← Alpha.decode 8 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (abbreviatedIssueCode, bytes) ← Alpha.decode 9 bytes
  let (abbreviatedIssueName, bytes) ← Alpha.decode 40 bytes
  let (abbreviatedIssueNameInEn, bytes) ← Alpha.decode 40 bytes
  let (groupNumber, bytes) ← Alpha.decode 5 bytes
  let (marketOperationProductId, bytes) ← Alpha.decode 3 bytes
  let (securityGroupId, bytes) ← Alpha.decode 2 bytes
  let (unitTrading, bytes) ← Alpha.decode 1 bytes
  let (rightsTypeCode, bytes) ← Alpha.decode 2 bytes
  let (parValueTypeCode, bytes) ← Alpha.decode 2 bytes
  let (anIssueOfWhichBasePriceIsSettledWithATodaysSinglePrice, bytes) ← Alpha.decode 1 bytes
  let (reevaluationReasonCode, bytes) ← Alpha.decode 2 bytes
  let (basePriceChange, bytes) ← Alpha.decode 1 bytes
  let (randomEndTriggerCode, bytes) ← Alpha.decode 1 bytes
  let (marketAlert, bytes) ← Alpha.decode 1 bytes
  let (marketAlertTypeCode, bytes) ← Alpha.decode 2 bytes
  let (koreaCorporateGovernanceStockPriceIndexKogi, bytes) ← Alpha.decode 1 bytes
  let (issueForAdministration, bytes) ← Alpha.decode 1 bytes
  let (unfaithfulDisclosure, bytes) ← Alpha.decode 1 bytes
  let (backdoorListing, bytes) ← Alpha.decode 1 bytes
  let (tradingHalt, bytes) ← Alpha.decode 1 bytes
  let (industryId, bytes) ← Alpha.decode 10 bytes
  let (smallMediumSizedBusiness, bytes) ← Alpha.decode 1 bytes
  let (sectionTypeCode, bytes) ← Alpha.decode 1 bytes
  let (investmentInstitutionTypeCode, bytes) ← Alpha.decode 1 bytes
  let (basePrice, bytes) ← Alpha.decode 11 bytes
  let (yesterdaysClosingPriceTypeCodeKrx, bytes) ← Alpha.decode 1 bytes
  let (yesterdaysClosingPriceKrx, bytes) ← Alpha.decode 11 bytes
  let (yesterdaysAccumulatedTradingAmount, bytes) ← Alpha.decode 12 bytes
  let (yesterdaysAccumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (upperLimitPrice, bytes) ← Alpha.decode 11 bytes
  let (lowerLimitPrice, bytes) ← Alpha.decode 11 bytes
  let (substitutePriceOfSecurities, bytes) ← Alpha.decode 11 bytes
  let (parValue, bytes) ← Alpha.decode 11 bytes
  let (issuingPrice, bytes) ← Alpha.decode 11 bytes
  let (listingDate, bytes) ← Alpha.decode 8 bytes
  let (numberOfListedShares, bytes) ← Alpha.decode 16 bytes
  let (liquidationTrade, bytes) ← Alpha.decode 1 bytes
  let (theEstablishmentDate, bytes) ← Alpha.decode 8 bytes
  let (maturityDate, bytes) ← Alpha.decode 8 bytes
  let (exercisingPeriod, bytes) ← Alpha.decode 8 bytes
  let (expirationDateForRight, bytes) ← Alpha.decode 8 bytes
  let (exercisePriceOfElwOrBw, bytes) ← Alpha.decode 13 bytes
  let (capital, bytes) ← Alpha.decode 22 bytes
  let (creditOrderPossibility, bytes) ← Alpha.decode 1 bytes
  let (limitOrderPermissionTypeCode, bytes) ← Alpha.decode 5 bytes
  let (marketPriceOrderPermissionTypeCode, bytes) ← Alpha.decode 5 bytes
  let (conditionedOrderPermissionTypeCode, bytes) ← Alpha.decode 5 bytes
  let (bestFavorableOrderPermissionTypeCode, bytes) ← Alpha.decode 5 bytes
  let (firstBestOrderPermissionType, bytes) ← Alpha.decode 5 bytes
  let (midPriceOrderPermissionTypeCode, bytes) ← Alpha.decode 5 bytes
  let (stopLimitPriceOrderPermissionTypeCode, bytes) ← Alpha.decode 5 bytes
  let (capitalIncreaseTypeCode, bytes) ← Alpha.decode 2 bytes
  let (otherStockTypeCode, bytes) ← Alpha.decode 1 bytes
  let (nationalStock, bytes) ← Alpha.decode 1 bytes
  let (appraisedPrice, bytes) ← Alpha.decode 11 bytes
  let (lowestOrderPrice, bytes) ← Alpha.decode 11 bytes
  let (highestOrderPrice, bytes) ← Alpha.decode 11 bytes
  let (unitOfVolumeInMainBoard, bytes) ← Alpha.decode 11 bytes
  let (lotSizeAfterhoursTrading, bytes) ← Alpha.decode 11 bytes
  let (reiTsTypeCode, bytes) ← Alpha.decode 1 bytes
  let (targetStockIsinCode, bytes) ← Alpha.decode 12 bytes
  let (currencyIsoCode, bytes) ← Alpha.decode 3 bytes
  let (countryCode, bytes) ← Alpha.decode 3 bytes
  let (marketMakingPossibility, bytes) ← Alpha.decode 1 bytes
  let (closingPriceTradingPossibilityInTheAfterHours, bytes) ← Alpha.decode 1 bytes
  let (closingPriceTradingInThePreopeningMarket, bytes) ← Alpha.decode 1 bytes
  let (blockTradingInThePreopeningMarket, bytes) ← Alpha.decode 1 bytes
  let (basketTradingInThePreopeningMarket, bytes) ← Alpha.decode 1 bytes
  let (announcementOfEstimatedTradingPrice, bytes) ← Alpha.decode 1 bytes
  let (shortSelling, bytes) ← Alpha.decode 1 bytes
  let (etfTrackingDifference, bytes) ← Alpha.decode 13 bytes
  let (regs, bytes) ← Alpha.decode 1 bytes
  let (spac, bytes) ← Alpha.decode 1 bytes
  let (taxTypeCode, bytes) ← Alpha.decode 1 bytes
  let (appraisalRatioOfSubstitutePrice, bytes) ← Alpha.decode 13 bytes
  let (investmentCautionIssue, bytes) ← Alpha.decode 1 bytes
  let (delistingDate, bytes) ← Alpha.decode 8 bytes
  let (shorttermOverheatIssueTypeCode, bytes) ← Alpha.decode 1 bytes
  let (etfReplicationMethodsTypeCode, bytes) ← Alpha.decode 1 bytes
  let (expirationDate, bytes) ← Alpha.decode 8 bytes
  let (distributionTypeCode, bytes) ← Alpha.decode 2 bytes
  let (calculationOfRedemptionPriceStartDate, bytes) ← Alpha.decode 8 bytes
  let (calculationOfRedemptionPriceEndDate, bytes) ← Alpha.decode 8 bytes
  let (etpProductTypeCode, bytes) ← Alpha.decode 1 bytes
  let (indexCalculationInstitutionTypeCode, bytes) ← Alpha.decode 2 bytes
  let (indexMarketClassificationId, bytes) ← Alpha.decode 6 bytes
  let (indexSequenceNumber, bytes) ← Alpha.decode 3 bytes
  let (trackingIndexLeverageInverseTypeCode, bytes) ← Alpha.decode 2 bytes
  let (referenceIndexLeverageInverseTypeCode, bytes) ← Alpha.decode 2 bytes
  let (indexAssetClassificationId1, bytes) ← Alpha.decode 6 bytes
  let (indexAssetClassificationId2, bytes) ← Alpha.decode 6 bytes
  let (ipoUnderwriterMemberNumber, bytes) ← Alpha.decode 5 bytes
  let (lpOrder, bytes) ← Alpha.decode 1 bytes
  let (lowLiquidity, bytes) ← Alpha.decode 1 bytes
  let (abnormalRise, bytes) ← Alpha.decode 1 bytes
  let (upperLimitQuantity, bytes) ← Alpha.decode 23 bytes
  let (investmentPrecautionIssue, bytes) ← Alpha.decode 1 bytes
  let (preferredStocksWithLesserShares, bytes) ← Alpha.decode 1 bytes
  let (spacMerger, bytes) ← Alpha.decode 1 bytes
  let (segmentTypeCode, bytes) ← Alpha.decode 1 bytes
  let (afterMarketPossibility, bytes) ← Alpha.decode 1 bytes
  let (choiceOnCompetitiveTrading, bytes) ← Alpha.decode 1 bytes
  let (limitOnCompetitiveTradingVolume, bytes) ← Alpha.decode 1 bytes
  let (occurrenceOfReasonsProhibitingCompetitiveTrading, bytes) ← Alpha.decode 1 bytes
  let (approvalOnCompetitiveTrading, bytes) ← Alpha.decode 1 bytes
  let (approvalOnNegotiationTrading, bytes) ← Alpha.decode 1 bytes
  let (yesterdaysClosingPriceTypeCodeNxt, bytes) ← Alpha.decode 1 bytes
  let (yesterdaysClosingPriceNxt, bytes) ← Alpha.decode 11 bytes
  let (competitionBoardTradePermissionCode, bytes) ← Alpha.decode 5 bytes
  let (negotiationPossibleOrNotBeforeMainMarket, bytes) ← Alpha.decode 1 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, totalNumberOfInstrumentsOfTheContract, businessDate, isinCode, aDesignatedNumberForAnIssueFromKrx, abbreviatedIssueCode, abbreviatedIssueName, abbreviatedIssueNameInEn, groupNumber, marketOperationProductId, securityGroupId, unitTrading, rightsTypeCode, parValueTypeCode, anIssueOfWhichBasePriceIsSettledWithATodaysSinglePrice, reevaluationReasonCode, basePriceChange, randomEndTriggerCode, marketAlert, marketAlertTypeCode, koreaCorporateGovernanceStockPriceIndexKogi, issueForAdministration, unfaithfulDisclosure, backdoorListing, tradingHalt, industryId, smallMediumSizedBusiness, sectionTypeCode, investmentInstitutionTypeCode, basePrice, yesterdaysClosingPriceTypeCodeKrx, yesterdaysClosingPriceKrx, yesterdaysAccumulatedTradingAmount, yesterdaysAccumulatedTradingValue, upperLimitPrice, lowerLimitPrice, substitutePriceOfSecurities, parValue, issuingPrice, listingDate, numberOfListedShares, liquidationTrade, theEstablishmentDate, maturityDate, exercisingPeriod, expirationDateForRight, exercisePriceOfElwOrBw, capital, creditOrderPossibility, limitOrderPermissionTypeCode, marketPriceOrderPermissionTypeCode, conditionedOrderPermissionTypeCode, bestFavorableOrderPermissionTypeCode, firstBestOrderPermissionType, midPriceOrderPermissionTypeCode, stopLimitPriceOrderPermissionTypeCode, capitalIncreaseTypeCode, otherStockTypeCode, nationalStock, appraisedPrice, lowestOrderPrice, highestOrderPrice, unitOfVolumeInMainBoard, lotSizeAfterhoursTrading, reiTsTypeCode, targetStockIsinCode, currencyIsoCode, countryCode, marketMakingPossibility, closingPriceTradingPossibilityInTheAfterHours, closingPriceTradingInThePreopeningMarket, blockTradingInThePreopeningMarket, basketTradingInThePreopeningMarket, announcementOfEstimatedTradingPrice, shortSelling, etfTrackingDifference, regs, spac, taxTypeCode, appraisalRatioOfSubstitutePrice, investmentCautionIssue, delistingDate, shorttermOverheatIssueTypeCode, etfReplicationMethodsTypeCode, expirationDate, distributionTypeCode, calculationOfRedemptionPriceStartDate, calculationOfRedemptionPriceEndDate, etpProductTypeCode, indexCalculationInstitutionTypeCode, indexMarketClassificationId, indexSequenceNumber, trackingIndexLeverageInverseTypeCode, referenceIndexLeverageInverseTypeCode, indexAssetClassificationId1, indexAssetClassificationId2, ipoUnderwriterMemberNumber, lpOrder, lowLiquidity, abnormalRise, upperLimitQuantity, investmentPrecautionIssue, preferredStocksWithLesserShares, spacMerger, segmentTypeCode, afterMarketPossibility, choiceOnCompetitiveTrading, limitOnCompetitiveTradingVolume, occurrenceOfReasonsProhibitingCompetitiveTrading, approvalOnCompetitiveTrading, approvalOnNegotiationTrading, yesterdaysClosingPriceTypeCodeNxt, yesterdaysClosingPriceNxt, competitionBoardTradePermissionCode, negotiationPossibleOrNotBeforeMainMarket, endKeyword }, bytes)

@[simp] theorem encode_length (message : EquitiesBatchDataMessage) : (encode message).length = 649 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EquitiesBatchDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : EquitiesBatchDataMessage) (rest : List UInt8) :
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

end EquitiesBatchDataMessage

/-- Member Information Message: 202 bytes -/
structure MemberInformationMessage where
  messageSequenceNumber : Alpha 8
  businessDate : Alpha 8
  marketParticipantNumber : Alpha 5
  nameOfAMarketParticipantInKr : Alpha 80
  nameOfAMarketParticipantInEn : Alpha 80
  anAbbreviatedNameOfAMarketParticipantInKr : Alpha 20
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace MemberInformationMessage

def encode (message : MemberInformationMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.businessDate
    ++ (Alpha.encode message.marketParticipantNumber
    ++ (Alpha.encode message.nameOfAMarketParticipantInKr
    ++ (Alpha.encode message.nameOfAMarketParticipantInEn
    ++ (Alpha.encode message.anAbbreviatedNameOfAMarketParticipantInKr
    ++ (Alpha.encode message.endKeyword))))))

def decode (bytes : List UInt8) : Option (MemberInformationMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (businessDate, bytes) ← Alpha.decode 8 bytes
  let (marketParticipantNumber, bytes) ← Alpha.decode 5 bytes
  let (nameOfAMarketParticipantInKr, bytes) ← Alpha.decode 80 bytes
  let (nameOfAMarketParticipantInEn, bytes) ← Alpha.decode 80 bytes
  let (anAbbreviatedNameOfAMarketParticipantInKr, bytes) ← Alpha.decode 20 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, businessDate, marketParticipantNumber, nameOfAMarketParticipantInKr, nameOfAMarketParticipantInEn, anAbbreviatedNameOfAMarketParticipantInKr, endKeyword }, bytes)

@[simp] theorem encode_length (message : MemberInformationMessage) : (encode message).length = 202 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MemberInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MemberInformationMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end MemberInformationMessage

/-- Issue Event Message: 43 bytes -/
structure IssueEventMessage where
  messageSequenceNumber : Alpha 8
  isinCode : Alpha 12
  eventTypeCode : Alpha 2
  eventReasonCode : Alpha 4
  eventStartDate : Alpha 8
  eventEndDate : Alpha 8
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace IssueEventMessage

def encode (message : IssueEventMessage) : List UInt8 :=
  Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.eventTypeCode
    ++ (Alpha.encode message.eventReasonCode
    ++ (Alpha.encode message.eventStartDate
    ++ (Alpha.encode message.eventEndDate
    ++ (Alpha.encode message.endKeyword))))))

def decode (bytes : List UInt8) : Option (IssueEventMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (eventTypeCode, bytes) ← Alpha.decode 2 bytes
  let (eventReasonCode, bytes) ← Alpha.decode 4 bytes
  let (eventStartDate, bytes) ← Alpha.decode 8 bytes
  let (eventEndDate, bytes) ← Alpha.decode 8 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ messageSequenceNumber, isinCode, eventTypeCode, eventReasonCode, eventStartDate, eventEndDate, endKeyword }, bytes)

@[simp] theorem encode_length (message : IssueEventMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : IssueEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueEventMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end IssueEventMessage

/-- Block Basket Trade Data Message: 55 bytes -/
structure BlockBasketTradeDataMessage where
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  accumulatedTradingVolume : Alpha 12
  accumulatedTradingValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace BlockBasketTradeDataMessage

def encode (message : BlockBasketTradeDataMessage) : List UInt8 :=
  Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.accumulatedTradingVolume
    ++ (Alpha.encode message.accumulatedTradingValue
    ++ (Alpha.encode message.endKeyword)))))

def decode (bytes : List UInt8) : Option (BlockBasketTradeDataMessage × List UInt8) := do
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (accumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, accumulatedTradingVolume, accumulatedTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : BlockBasketTradeDataMessage) : (encode message).length = 55 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BlockBasketTradeDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BlockBasketTradeDataMessage) (rest : List UInt8) :
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

end BlockBasketTradeDataMessage

/-- Investor Activities Per An Issue Eod Message: 91 bytes -/
structure InvestorActivitiesPerAnIssueEodMessage where
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : Alpha 6
  investorCode : Alpha 4
  accumulatedAskTradingVolume : Alpha 12
  accumulatedAskTradingValue : Alpha 22
  accumulatedBidTradingVolume : Alpha 12
  accumulatedBidTradingValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace InvestorActivitiesPerAnIssueEodMessage

def encode (message : InvestorActivitiesPerAnIssueEodMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.investorCode
    ++ (Alpha.encode message.accumulatedAskTradingVolume
    ++ (Alpha.encode message.accumulatedAskTradingValue
    ++ (Alpha.encode message.accumulatedBidTradingVolume
    ++ (Alpha.encode message.accumulatedBidTradingValue
    ++ (Alpha.encode message.endKeyword)))))))

def decode (bytes : List UInt8) : Option (InvestorActivitiesPerAnIssueEodMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← Alpha.decode 6 bytes
  let (investorCode, bytes) ← Alpha.decode 4 bytes
  let (accumulatedAskTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedAskTradingValue, bytes) ← Alpha.decode 22 bytes
  let (accumulatedBidTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedBidTradingValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ isinCode, aDesignatedNumberForAnIssueFromKrx, investorCode, accumulatedAskTradingVolume, accumulatedAskTradingValue, accumulatedBidTradingVolume, accumulatedBidTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : InvestorActivitiesPerAnIssueEodMessage) : (encode message).length = 91 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : InvestorActivitiesPerAnIssueEodMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InvestorActivitiesPerAnIssueEodMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end InvestorActivitiesPerAnIssueEodMessage

/-- Short Selling Message: 115 bytes -/
structure ShortSellingMessage where
  isinCode : Alpha 12
  coveredShortSellingTradingVolume : Alpha 12
  coveredShortSellingTradingValue : Alpha 22
  uptickRuleAppliedCoveredShortSellingTradingVolume : Alpha 12
  uptickRuleAppliedCoveredShortSellingTradingValue : Alpha 22
  uptickRuleUnappliedCoveredShortSellingTradingVolume : Alpha 12
  uptickRuleUnappliedCoveredShortSellingTradingValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace ShortSellingMessage

def encode (message : ShortSellingMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.coveredShortSellingTradingVolume
    ++ (Alpha.encode message.coveredShortSellingTradingValue
    ++ (Alpha.encode message.uptickRuleAppliedCoveredShortSellingTradingVolume
    ++ (Alpha.encode message.uptickRuleAppliedCoveredShortSellingTradingValue
    ++ (Alpha.encode message.uptickRuleUnappliedCoveredShortSellingTradingVolume
    ++ (Alpha.encode message.uptickRuleUnappliedCoveredShortSellingTradingValue
    ++ (Alpha.encode message.endKeyword)))))))

def decode (bytes : List UInt8) : Option (ShortSellingMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (coveredShortSellingTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (coveredShortSellingTradingValue, bytes) ← Alpha.decode 22 bytes
  let (uptickRuleAppliedCoveredShortSellingTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (uptickRuleAppliedCoveredShortSellingTradingValue, bytes) ← Alpha.decode 22 bytes
  let (uptickRuleUnappliedCoveredShortSellingTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (uptickRuleUnappliedCoveredShortSellingTradingValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ isinCode, coveredShortSellingTradingVolume, coveredShortSellingTradingValue, uptickRuleAppliedCoveredShortSellingTradingVolume, uptickRuleAppliedCoveredShortSellingTradingValue, uptickRuleUnappliedCoveredShortSellingTradingVolume, uptickRuleUnappliedCoveredShortSellingTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : ShortSellingMessage) : (encode message).length = 115 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ShortSellingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortSellingMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ShortSellingMessage

/-- Brokers Acitity Information Message: 86 bytes -/
structure BrokersAcitityInformationMessage where
  isinCode : Alpha 12
  memberNumber : Alpha 5
  accumulatedAskTradingVolume : Alpha 12
  accumulatedAskTradingValue : Alpha 22
  accumulatedBidTradingVolume : Alpha 12
  accumulatedBidTradingValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace BrokersAcitityInformationMessage

def encode (message : BrokersAcitityInformationMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.memberNumber
    ++ (Alpha.encode message.accumulatedAskTradingVolume
    ++ (Alpha.encode message.accumulatedAskTradingValue
    ++ (Alpha.encode message.accumulatedBidTradingVolume
    ++ (Alpha.encode message.accumulatedBidTradingValue
    ++ (Alpha.encode message.endKeyword))))))

def decode (bytes : List UInt8) : Option (BrokersAcitityInformationMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (memberNumber, bytes) ← Alpha.decode 5 bytes
  let (accumulatedAskTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedAskTradingValue, bytes) ← Alpha.decode 22 bytes
  let (accumulatedBidTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (accumulatedBidTradingValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ isinCode, memberNumber, accumulatedAskTradingVolume, accumulatedAskTradingValue, accumulatedBidTradingVolume, accumulatedBidTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : BrokersAcitityInformationMessage) : (encode message).length = 86 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BrokersAcitityInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokersAcitityInformationMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end BrokersAcitityInformationMessage

/-- Trading Activity By Session Per An Issue Message: 120 bytes -/
structure TradingActivityBySessionPerAnIssueMessage where
  isinCode : Alpha 12
  totalNumberOfTradableIssuesOnCompetitiveTrading : Alpha 5
  premarketAccumulatedTradingVolume : Alpha 12
  premarketAccumulatedTradingValue : Alpha 22
  mainmarketAccumulatedTradingVolume : Alpha 12
  mainmarketAccumulatedTradingValue : Alpha 22
  aftermarketAccumulatedTradingVolume : Alpha 12
  aftermarketAccumulatedTradingValue : Alpha 22
  endKeyword : Alpha 1
  deriving DecidableEq, Repr

namespace TradingActivityBySessionPerAnIssueMessage

def encode (message : TradingActivityBySessionPerAnIssueMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.totalNumberOfTradableIssuesOnCompetitiveTrading
    ++ (Alpha.encode message.premarketAccumulatedTradingVolume
    ++ (Alpha.encode message.premarketAccumulatedTradingValue
    ++ (Alpha.encode message.mainmarketAccumulatedTradingVolume
    ++ (Alpha.encode message.mainmarketAccumulatedTradingValue
    ++ (Alpha.encode message.aftermarketAccumulatedTradingVolume
    ++ (Alpha.encode message.aftermarketAccumulatedTradingValue
    ++ (Alpha.encode message.endKeyword))))))))

def decode (bytes : List UInt8) : Option (TradingActivityBySessionPerAnIssueMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (totalNumberOfTradableIssuesOnCompetitiveTrading, bytes) ← Alpha.decode 5 bytes
  let (premarketAccumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (premarketAccumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (mainmarketAccumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (mainmarketAccumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (aftermarketAccumulatedTradingVolume, bytes) ← Alpha.decode 12 bytes
  let (aftermarketAccumulatedTradingValue, bytes) ← Alpha.decode 22 bytes
  let (endKeyword, bytes) ← Alpha.decode 1 bytes
  pure ({ isinCode, totalNumberOfTradableIssuesOnCompetitiveTrading, premarketAccumulatedTradingVolume, premarketAccumulatedTradingValue, mainmarketAccumulatedTradingVolume, mainmarketAccumulatedTradingValue, aftermarketAccumulatedTradingVolume, aftermarketAccumulatedTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : TradingActivityBySessionPerAnIssueMessage) : (encode message).length = 120 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TradingActivityBySessionPerAnIssueMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingActivityBySessionPerAnIssueMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradingActivityBySessionPerAnIssueMessage

/-- Any Payload, selected by TR Code -/
inductive Payload where
  | pollingDataMessage (message : PollingDataMessage) -- "I2500" 0x4932353030
  | securitiesQuoteMmLpQuotesIncluded10LevelMessage (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) -- "B753S" 0x4237353353
  | securitiesOrderFilledMessage (message : SecuritiesOrderFilledMessage) -- "A353S" 0x4133353353
  | marketOperationTsMessage (message : MarketOperationTsMessage) -- "A753S" 0x4137353353
  | issueClosingMessage (message : IssueClosingMessage) -- "A653S" 0x4136353353
  | triggeringRemovingViMessage (message : TriggeringRemovingViMessage) -- "R853S" 0x5238353353
  | closingPriceTradingQuoteMessage (message : ClosingPriceTradingQuoteMessage) -- "E153S" 0x4531353353
  | equitiesSnapshotMmLpQuotesIncluded10LevelMessage (message : EquitiesSnapshotMmLpQuotesIncluded10LevelMessage) -- "B253S" 0x4232353353
  | investorActivitiesPerCommoditiesMessage (message : InvestorActivitiesPerCommoditiesMessage) -- "IC53S" 0x4943353353
  | etpConstituentsMessage (message : EtpConstituentsMessage) -- "V650S" 0x5636353053
  | etpConstituentsMessage297446748243 (message : EtpConstituentsMessage) -- "EA50S" 0x4541353053
  | mmLpInformationMessage (message : MmLpInformationMessage) -- "I753S" 0x4937353353
  | mmLpInformationMessage297463526227 (message : MmLpInformationMessage) -- "EB53S" 0x4542353353
  | marketOperationScheduleMessage (message : MarketOperationScheduleMessage) -- "M453S" 0x4D34353353
  | memberFirmImposingLiftingSanctionsMessage (message : MemberFirmImposingLiftingSanctionsMessage) -- "R350S" 0x5233353053
  | topFiveTradersActivitiesMessage (message : TopFiveTradersActivitiesMessage) -- "B953S" 0x4239353353
  | equitiesBatchDataMessage (message : EquitiesBatchDataMessage) -- "A053S" 0x4130353353
  | equitiesBatchDataMessage297161536339 (message : EquitiesBatchDataMessage) -- "E053S" 0x4530353353
  | memberInformationMessage (message : MemberInformationMessage) -- "M950S" 0x4D39353053
  | memberInformationMessage297295753299 (message : MemberInformationMessage) -- "E850S" 0x4538353053
  | issueEventMessage (message : IssueEventMessage) -- "I653S" 0x4936353353
  | issueEventMessage297262199635 (message : IssueEventMessage) -- "E653S" 0x4536353353
  | blockBasketTradeDataMessage (message : BlockBasketTradeDataMessage) -- "C453S" 0x4334353353
  | investorActivitiesPerAnIssueEodMessage (message : InvestorActivitiesPerAnIssueEodMessage) -- "C153S" 0x4331353353
  | shortSellingMessage (message : ShortSellingMessage) -- "I853S" 0x4938353353
  | brokersAcitityInformationMessage (message : BrokersAcitityInformationMessage) -- "E253S" 0x4532353353
  | tradingActivityBySessionPerAnIssueMessage (message : TradingActivityBySessionPerAnIssueMessage) -- "E353S" 0x4533353353
  deriving DecidableEq, Repr

namespace Payload

/-- The TR Code each message is sent under -/
def tag : Payload → BitVec 40
  | .pollingDataMessage _ => 314374959152
  | .securitiesQuoteMmLpQuotesIncluded10LevelMessage _ => 284394074963
  | .securitiesOrderFilledMessage _ => 280031998803
  | .marketOperationTsMessage _ => 280099107667
  | .issueClosingMessage _ => 280082330451
  | .triggeringRemovingViMessage _ => 353130328915
  | .closingPriceTradingQuoteMessage _ => 297178313555
  | .equitiesSnapshotMmLpQuotesIncluded10LevelMessage _ => 284310188883
  | .investorActivitiesPerCommoditiesMessage _ => 314660172627
  | .etpConstituentsMessage _ => 370276642899
  | .etpConstituentsMessage297446748243 _ => 297446748243
  | .mmLpInformationMessage _ => 314458846035
  | .mmLpInformationMessage297463526227 _ => 297463526227
  | .marketOperationScheduleMessage _ => 331588383571
  | .memberFirmImposingLiftingSanctionsMessage _ => 353046442067
  | .topFiveTradersActivitiesMessage _ => 284427629395
  | .equitiesBatchDataMessage _ => 279981667155
  | .equitiesBatchDataMessage297161536339 _ => 297161536339
  | .memberInformationMessage _ => 331672268883
  | .memberInformationMessage297295753299 _ => 297295753299
  | .issueEventMessage _ => 314442068819
  | .issueEventMessage297262199635 _ => 297262199635
  | .blockBasketTradeDataMessage _ => 288638710611
  | .investorActivitiesPerAnIssueEodMessage _ => 288588378963
  | .shortSellingMessage _ => 314475623251
  | .brokersAcitityInformationMessage _ => 297195090771
  | .tradingActivityBySessionPerAnIssueMessage _ => 297211867987

def encode : Payload → List UInt8
  | .pollingDataMessage message => PollingDataMessage.encode message
  | .securitiesQuoteMmLpQuotesIncluded10LevelMessage message => SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.encode message
  | .securitiesOrderFilledMessage message => SecuritiesOrderFilledMessage.encode message
  | .marketOperationTsMessage message => MarketOperationTsMessage.encode message
  | .issueClosingMessage message => IssueClosingMessage.encode message
  | .triggeringRemovingViMessage message => TriggeringRemovingViMessage.encode message
  | .closingPriceTradingQuoteMessage message => ClosingPriceTradingQuoteMessage.encode message
  | .equitiesSnapshotMmLpQuotesIncluded10LevelMessage message => EquitiesSnapshotMmLpQuotesIncluded10LevelMessage.encode message
  | .investorActivitiesPerCommoditiesMessage message => InvestorActivitiesPerCommoditiesMessage.encode message
  | .etpConstituentsMessage message => EtpConstituentsMessage.encode message
  | .etpConstituentsMessage297446748243 message => EtpConstituentsMessage.encode message
  | .mmLpInformationMessage message => MmLpInformationMessage.encode message
  | .mmLpInformationMessage297463526227 message => MmLpInformationMessage.encode message
  | .marketOperationScheduleMessage message => MarketOperationScheduleMessage.encode message
  | .memberFirmImposingLiftingSanctionsMessage message => MemberFirmImposingLiftingSanctionsMessage.encode message
  | .topFiveTradersActivitiesMessage message => TopFiveTradersActivitiesMessage.encode message
  | .equitiesBatchDataMessage message => EquitiesBatchDataMessage.encode message
  | .equitiesBatchDataMessage297161536339 message => EquitiesBatchDataMessage.encode message
  | .memberInformationMessage message => MemberInformationMessage.encode message
  | .memberInformationMessage297295753299 message => MemberInformationMessage.encode message
  | .issueEventMessage message => IssueEventMessage.encode message
  | .issueEventMessage297262199635 message => IssueEventMessage.encode message
  | .blockBasketTradeDataMessage message => BlockBasketTradeDataMessage.encode message
  | .investorActivitiesPerAnIssueEodMessage message => InvestorActivitiesPerAnIssueEodMessage.encode message
  | .shortSellingMessage message => ShortSellingMessage.encode message
  | .brokersAcitityInformationMessage message => BrokersAcitityInformationMessage.encode message
  | .tradingActivityBySessionPerAnIssueMessage message => TradingActivityBySessionPerAnIssueMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 930 := by
  cases message with
  | pollingDataMessage inner =>
    simp only [encode, PollingDataMessage.encode_length]
    omega
  | securitiesQuoteMmLpQuotesIncluded10LevelMessage inner =>
    simp only [encode, SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.encode_length]
    omega
  | securitiesOrderFilledMessage inner =>
    simp only [encode, SecuritiesOrderFilledMessage.encode_length]
    omega
  | marketOperationTsMessage inner =>
    simp only [encode, MarketOperationTsMessage.encode_length]
    omega
  | issueClosingMessage inner =>
    simp only [encode, IssueClosingMessage.encode_length]
    omega
  | triggeringRemovingViMessage inner =>
    simp only [encode, TriggeringRemovingViMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage inner =>
    simp only [encode, ClosingPriceTradingQuoteMessage.encode_length]
    omega
  | equitiesSnapshotMmLpQuotesIncluded10LevelMessage inner =>
    simp only [encode, EquitiesSnapshotMmLpQuotesIncluded10LevelMessage.encode_length]
    omega
  | investorActivitiesPerCommoditiesMessage inner =>
    simp only [encode, InvestorActivitiesPerCommoditiesMessage.encode_length]
    omega
  | etpConstituentsMessage inner =>
    simp only [encode, EtpConstituentsMessage.encode_length]
    omega
  | etpConstituentsMessage297446748243 inner =>
    simp only [encode, EtpConstituentsMessage.encode_length]
    omega
  | mmLpInformationMessage inner =>
    simp only [encode, MmLpInformationMessage.encode_length]
    omega
  | mmLpInformationMessage297463526227 inner =>
    simp only [encode, MmLpInformationMessage.encode_length]
    omega
  | marketOperationScheduleMessage inner =>
    simp only [encode, MarketOperationScheduleMessage.encode_length]
    omega
  | memberFirmImposingLiftingSanctionsMessage inner =>
    simp only [encode, MemberFirmImposingLiftingSanctionsMessage.encode_length]
    omega
  | topFiveTradersActivitiesMessage inner =>
    simp only [encode, TopFiveTradersActivitiesMessage.encode_length]
    omega
  | equitiesBatchDataMessage inner =>
    simp only [encode, EquitiesBatchDataMessage.encode_length]
    omega
  | equitiesBatchDataMessage297161536339 inner =>
    simp only [encode, EquitiesBatchDataMessage.encode_length]
    omega
  | memberInformationMessage inner =>
    simp only [encode, MemberInformationMessage.encode_length]
    omega
  | memberInformationMessage297295753299 inner =>
    simp only [encode, MemberInformationMessage.encode_length]
    omega
  | issueEventMessage inner =>
    simp only [encode, IssueEventMessage.encode_length]
    omega
  | issueEventMessage297262199635 inner =>
    simp only [encode, IssueEventMessage.encode_length]
    omega
  | blockBasketTradeDataMessage inner =>
    simp only [encode, BlockBasketTradeDataMessage.encode_length]
    omega
  | investorActivitiesPerAnIssueEodMessage inner =>
    simp only [encode, InvestorActivitiesPerAnIssueEodMessage.encode_length]
    omega
  | shortSellingMessage inner =>
    simp only [encode, ShortSellingMessage.encode_length]
    omega
  | brokersAcitityInformationMessage inner =>
    simp only [encode, BrokersAcitityInformationMessage.encode_length]
    omega
  | tradingActivityBySessionPerAnIssueMessage inner =>
    simp only [encode, TradingActivityBySessionPerAnIssueMessage.encode_length]
    omega

def decode (tag : BitVec 40) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 314374959152 then (PollingDataMessage.decode bytes).map fun (message, rest) => (.pollingDataMessage message, rest)
  else if tag = 284394074963 then (SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.decode bytes).map fun (message, rest) => (.securitiesQuoteMmLpQuotesIncluded10LevelMessage message, rest)
  else if tag = 280031998803 then (SecuritiesOrderFilledMessage.decode bytes).map fun (message, rest) => (.securitiesOrderFilledMessage message, rest)
  else if tag = 280099107667 then (MarketOperationTsMessage.decode bytes).map fun (message, rest) => (.marketOperationTsMessage message, rest)
  else if tag = 280082330451 then (IssueClosingMessage.decode bytes).map fun (message, rest) => (.issueClosingMessage message, rest)
  else if tag = 353130328915 then (TriggeringRemovingViMessage.decode bytes).map fun (message, rest) => (.triggeringRemovingViMessage message, rest)
  else if tag = 297178313555 then (ClosingPriceTradingQuoteMessage.decode bytes).map fun (message, rest) => (.closingPriceTradingQuoteMessage message, rest)
  else if tag = 284310188883 then (EquitiesSnapshotMmLpQuotesIncluded10LevelMessage.decode bytes).map fun (message, rest) => (.equitiesSnapshotMmLpQuotesIncluded10LevelMessage message, rest)
  else if tag = 314660172627 then (InvestorActivitiesPerCommoditiesMessage.decode bytes).map fun (message, rest) => (.investorActivitiesPerCommoditiesMessage message, rest)
  else if tag = 370276642899 then (EtpConstituentsMessage.decode bytes).map fun (message, rest) => (.etpConstituentsMessage message, rest)
  else if tag = 297446748243 then (EtpConstituentsMessage.decode bytes).map fun (message, rest) => (.etpConstituentsMessage297446748243 message, rest)
  else if tag = 314458846035 then (MmLpInformationMessage.decode bytes).map fun (message, rest) => (.mmLpInformationMessage message, rest)
  else if tag = 297463526227 then (MmLpInformationMessage.decode bytes).map fun (message, rest) => (.mmLpInformationMessage297463526227 message, rest)
  else if tag = 331588383571 then (MarketOperationScheduleMessage.decode bytes).map fun (message, rest) => (.marketOperationScheduleMessage message, rest)
  else if tag = 353046442067 then (MemberFirmImposingLiftingSanctionsMessage.decode bytes).map fun (message, rest) => (.memberFirmImposingLiftingSanctionsMessage message, rest)
  else if tag = 284427629395 then (TopFiveTradersActivitiesMessage.decode bytes).map fun (message, rest) => (.topFiveTradersActivitiesMessage message, rest)
  else if tag = 279981667155 then (EquitiesBatchDataMessage.decode bytes).map fun (message, rest) => (.equitiesBatchDataMessage message, rest)
  else if tag = 297161536339 then (EquitiesBatchDataMessage.decode bytes).map fun (message, rest) => (.equitiesBatchDataMessage297161536339 message, rest)
  else if tag = 331672268883 then (MemberInformationMessage.decode bytes).map fun (message, rest) => (.memberInformationMessage message, rest)
  else if tag = 297295753299 then (MemberInformationMessage.decode bytes).map fun (message, rest) => (.memberInformationMessage297295753299 message, rest)
  else if tag = 314442068819 then (IssueEventMessage.decode bytes).map fun (message, rest) => (.issueEventMessage message, rest)
  else if tag = 297262199635 then (IssueEventMessage.decode bytes).map fun (message, rest) => (.issueEventMessage297262199635 message, rest)
  else if tag = 288638710611 then (BlockBasketTradeDataMessage.decode bytes).map fun (message, rest) => (.blockBasketTradeDataMessage message, rest)
  else if tag = 288588378963 then (InvestorActivitiesPerAnIssueEodMessage.decode bytes).map fun (message, rest) => (.investorActivitiesPerAnIssueEodMessage message, rest)
  else if tag = 314475623251 then (ShortSellingMessage.decode bytes).map fun (message, rest) => (.shortSellingMessage message, rest)
  else if tag = 297195090771 then (BrokersAcitityInformationMessage.decode bytes).map fun (message, rest) => (.brokersAcitityInformationMessage message, rest)
  else if tag = 297211867987 then (TradingActivityBySessionPerAnIssueMessage.decode bytes).map fun (message, rest) => (.tradingActivityBySessionPerAnIssueMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Packet -/
structure Packet where
  payload : Payload
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 5 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (trCode, bytes) ← decodeUInt 5 bytes
  let (payload, bytes) ← Payload.decode trCode bytes
  pure ({ payload }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 935 := by
  unfold encode
  cases message.payload with
  | pollingDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PollingDataMessage.encode_length]
    omega
  | securitiesQuoteMmLpQuotesIncluded10LevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.encode_length]
    omega
  | securitiesOrderFilledMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesOrderFilledMessage.encode_length]
    omega
  | marketOperationTsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationTsMessage.encode_length]
    omega
  | issueClosingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueClosingMessage.encode_length]
    omega
  | triggeringRemovingViMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TriggeringRemovingViMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ClosingPriceTradingQuoteMessage.encode_length]
    omega
  | equitiesSnapshotMmLpQuotesIncluded10LevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesSnapshotMmLpQuotesIncluded10LevelMessage.encode_length]
    omega
  | investorActivitiesPerCommoditiesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InvestorActivitiesPerCommoditiesMessage.encode_length]
    omega
  | etpConstituentsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EtpConstituentsMessage.encode_length]
    omega
  | etpConstituentsMessage297446748243 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EtpConstituentsMessage.encode_length]
    omega
  | mmLpInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MmLpInformationMessage.encode_length]
    omega
  | mmLpInformationMessage297463526227 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MmLpInformationMessage.encode_length]
    omega
  | marketOperationScheduleMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationScheduleMessage.encode_length]
    omega
  | memberFirmImposingLiftingSanctionsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MemberFirmImposingLiftingSanctionsMessage.encode_length]
    omega
  | topFiveTradersActivitiesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TopFiveTradersActivitiesMessage.encode_length]
    omega
  | equitiesBatchDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesBatchDataMessage.encode_length]
    omega
  | equitiesBatchDataMessage297161536339 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesBatchDataMessage.encode_length]
    omega
  | memberInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MemberInformationMessage.encode_length]
    omega
  | memberInformationMessage297295753299 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MemberInformationMessage.encode_length]
    omega
  | issueEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueEventMessage.encode_length]
    omega
  | issueEventMessage297262199635 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueEventMessage.encode_length]
    omega
  | blockBasketTradeDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BlockBasketTradeDataMessage.encode_length]
    omega
  | investorActivitiesPerAnIssueEodMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InvestorActivitiesPerAnIssueEodMessage.encode_length]
    omega
  | shortSellingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ShortSellingMessage.encode_length]
    omega
  | brokersAcitityInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BrokersAcitityInformationMessage.encode_length]
    omega
  | tradingActivityBySessionPerAnIssueMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingActivityBySessionPerAnIssueMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Packet

end Omi.NextradeNextradeEtpcommonNxtasciiV212
