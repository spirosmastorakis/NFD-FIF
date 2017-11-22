/* -*- Mode:C++; c-file-style:"gnu"; indent-tabs-mode:nil; -*- */
/*
 * Copyright (c) 2014-2017,  Regents of the University of California,
 *                           Arizona Board of Regents,
 *                           Colorado State University,
 *                           University Pierre & Marie Curie, Sorbonne University,
 *                           Washington University in St. Louis,
 *                           Beijing Institute of Technology,
 *                           The University of Memphis.
 *
 * This file is part of NFD (Named Data Networking Forwarding Daemon).
 * See AUTHORS.md for complete list of NFD authors and contributors.
 *
 * NFD is free software: you can redistribute it and/or modify it under the terms
 * of the GNU General Public License as published by the Free Software Foundation,
 * either version 3 of the License, or (at your option) any later version.
 *
 * NFD is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE.  See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * NFD, e.g., in COPYING.md file.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "fuzzy-strategy.hpp"
#include "algorithm.hpp"
#include "core/logger.hpp"

#include "ns3/ndnSIM/model/ndn-fuzzy-common.hpp"

namespace nfd {
namespace fw {

NFD_LOG_INIT("FuzzyStrategy");
NFD_REGISTER_STRATEGY(FuzzyStrategy);

const time::milliseconds FuzzyStrategy::RETX_SUPPRESSION_INITIAL(10);
const time::milliseconds FuzzyStrategy::RETX_SUPPRESSION_MAX(250);

FuzzyStrategy::FuzzyStrategy(Forwarder& forwarder, const Name& name)
  : Strategy(forwarder)
  , ProcessNackTraits(this)
  , m_retxSuppression(RETX_SUPPRESSION_INITIAL,
                      RetxSuppressionExponential::DEFAULT_MULTIPLIER,
                      RETX_SUPPRESSION_MAX)
  , m_waitAndFwd(false)
{
  ParsedInstanceName parsed = parseInstanceName(name);
  if (!parsed.parameters.empty()) {
    BOOST_THROW_EXCEPTION(std::invalid_argument("FuzzyStrategy does not accept parameters"));
  }
  if (parsed.version && *parsed.version != getStrategyName()[-1].toVersion()) {
    BOOST_THROW_EXCEPTION(std::invalid_argument(
      "BestRouteStrategy2 does not support version " + std::to_string(*parsed.version)));
  }
  this->setInstanceName(makeInstanceName(name, getStrategyName()));

  prepare_model(filename, (void*)&m_forwarder.initStruct);
  num_matches = 0;
  pendingInterestIndex = 0;
}

const Name&
FuzzyStrategy::getStrategyName()
{
  static Name strategyName("/localhost/nfd/strategy/fuzzy/%FD%05");
  return strategyName;
}

/** \brief determines whether a NextHop is eligible
 *  \param inFace incoming face of current Interest
 *  \param interest incoming Interest
 *  \param nexthop next hop
 *  \param pitEntry PIT entry
 *  \param wantUnused if true, NextHop must not have unexpired out-record
 *  \param now time::steady_clock::now(), ignored if !wantUnused
 */
static inline bool
isNextHopEligible(const Face& inFace, const Interest& interest,
                  const fib::NextHop& nexthop,
                  const shared_ptr<pit::Entry>& pitEntry,
                  bool wantUnused = false,
                  time::steady_clock::TimePoint now = time::steady_clock::TimePoint::min())
{
  const Face& outFace = nexthop.getFace();

  // do not forward back to the same face, unless it is ad hoc
  if (outFace.getId() == inFace.getId() && outFace.getLinkType() != ndn::nfd::LINK_TYPE_AD_HOC)
    return false;

  // forwarding would violate scope
  if (wouldViolateScope(inFace, interest, outFace))
    return false;

  if (wantUnused) {
    // nexthop must not have unexpired out-record
    pit::OutRecordCollection::iterator outRecord = pitEntry->getOutRecord(outFace);
    if (outRecord != pitEntry->out_end() && outRecord->getExpiry() > now) {
      return false;
    }
  }

  return true;
}

/** \brief pick an eligible NextHop with earliest out-record
 *  \note It is assumed that every nexthop has an out-record.
 */
static inline fib::NextHopList::const_iterator
findEligibleNextHopWithEarliestOutRecord(const Face& inFace, const Interest& interest,
                                         const fib::NextHopList& nexthops,
                                         const shared_ptr<pit::Entry>& pitEntry)
{
  fib::NextHopList::const_iterator found = nexthops.end();
  time::steady_clock::TimePoint earliestRenewed = time::steady_clock::TimePoint::max();
  for (fib::NextHopList::const_iterator it = nexthops.begin(); it != nexthops.end(); ++it) {
    if (!isNextHopEligible(inFace, interest, *it, pitEntry))
      continue;
    pit::OutRecordCollection::iterator outRecord = pitEntry->getOutRecord(it->getFace());
    BOOST_ASSERT(outRecord != pitEntry->out_end());
    if (outRecord->getLastRenewed() < earliestRenewed) {
      found = it;
      earliestRenewed = outRecord->getLastRenewed();
    }
  }
  return found;
}

void
FuzzyStrategy::afterReceiveInterest(const Face& inFace, const Interest& interest,
                                    const shared_ptr<pit::Entry>& pitEntry)
{
  NFD_LOG_DEBUG(interest << " in afterReceiveInterest");
  RetxSuppressionResult suppression = m_retxSuppression.decidePerPitEntry(*pitEntry);
  if (suppression == RetxSuppressionResult::SUPPRESS) {
    NFD_LOG_DEBUG(interest << " from=" << inFace.getId()
                           << " suppressed");
    return;
  }

  // try exact match first
  const fib::Entry& exactFibEntry = this->lookupFib(*pitEntry, nullptr);
  const fib::NextHopList& exactNexthops = exactFibEntry.getNextHops();
  fib::NextHopList::const_iterator exactIt = exactNexthops.end();

  exactIt = std::find_if(exactNexthops.begin(), exactNexthops.end(),
    bind(&isNextHopEligible, cref(inFace), interest, _1, pitEntry,
         false, time::steady_clock::TimePoint::min()));

  if (exactIt != exactNexthops.end()) {
    Face& outFace = exactIt->getFace();
    this->sendInterest(pitEntry, outFace, interest);
    NFD_LOG_DEBUG(interest << " from=" << inFace.getId()
                           << " exact match with newPitEntry-to=" << outFace.getId());
    return;
  }

  if (!interest.getForwardingHint().empty())
    beforeCSLookup(interest, num_matches, m_waitAndFwd, m_waitTime);

  bool resultFound = false;

  for (int i = 0; i < num_matches; i++) {
    // prepare name to be fuzzy matched
    shared_ptr<Name> fuzzyName = make_shared<Name>(interest.getName().getPrefix(COMP_INDEX_FUZZY));
    fuzzyName->append(m_forwarder.results.resultsArray[i].resultValue);
    for (int j = COMP_INDEX_FUZZY + 1; j < interest.getName().size(); j++) {
      fuzzyName->append(interest.getName().get(j));
    }
    NFD_LOG_DEBUG("Fuzzy Matching for name " << *fuzzyName);
    const fib::Entry& fibEntry = this->lookupFib(*pitEntry, fuzzyName);
    const fib::NextHopList& nexthops = fibEntry.getNextHops();
    fib::NextHopList::const_iterator it = nexthops.end();

    if (suppression == RetxSuppressionResult::NEW) {
      // forward to nexthop with lowest cost except downstream
      it = std::find_if(nexthops.begin(), nexthops.end(),
        bind(&isNextHopEligible, cref(inFace), interest, _1, pitEntry,
             false, time::steady_clock::TimePoint::min()));

      if (it == nexthops.end()) {
        continue;
      }

      if (interest.getForwardingHint().empty() && m_waitAndFwd) {
        int waitTime = m_waitTime * 1000;
        NFD_LOG_DEBUG(interest << " from=" << inFace.getId() << " initial match -- Retrying in " << waitTime << " ms");
        resultFormat resultsCopy;
        resultsCopy.nResultsToReturn = num_matches;
        for (int j = 0; j < num_matches; j++) {
          strcpy(resultsCopy.resultsArray[j].resultValue, m_forwarder.results.resultsArray[j].resultValue);
          resultsCopy.similarity[j] = m_forwarder.results.similarity[j];
          NFD_LOG_DEBUG("Result " << j << " is " << m_forwarder.results.resultsArray[j].resultValue);
        }
        m_pendingInterests.push_back(interest);
        scheduler::schedule(time::milliseconds(waitTime), bind(&FuzzyStrategy::retrySendingInterest, this, ref(inFace), ref(interest), pitEntry, resultsCopy, i));
        return;
      }

      resultFound = true;
      Face& outFace = it->getFace();
      Delegation del;
      del.name = Name(*fuzzyName);
      del.preference = 1;
      DelegationList list({del});
      const_cast<Interest&>(interest).setForwardingHint(list);
      this->sendInterest(pitEntry, outFace, interest);
      NFD_LOG_DEBUG(interest << " from=" << inFace.getId()
                             << " newPitEntry-to=" << outFace.getId());
      return;
    }
    else {
      // find an unused upstream with lowest cost except downstream
      it = std::find_if(nexthops.begin(), nexthops.end(),
                        bind(&isNextHopEligible, cref(inFace), interest, _1, pitEntry,
                             true, time::steady_clock::now()));
      if (it != nexthops.end()) {
        Face& outFace = it->getFace();
        this->sendInterest(pitEntry, outFace, interest);
        NFD_LOG_DEBUG(interest << " from=" << inFace.getId()
                               << " retransmit-unused-to=" << outFace.getId());
        return;
      }

      // find an eligible upstream that is used earliest
      it = findEligibleNextHopWithEarliestOutRecord(inFace, interest, nexthops, pitEntry);
      if (it == nexthops.end()) {
        NFD_LOG_DEBUG(interest << " from=" << inFace.getId() << " retransmitNoNextHop");
      }
      else {
        Face& outFace = it->getFace();
        this->sendInterest(pitEntry, outFace, interest);
        NFD_LOG_DEBUG(interest << " from=" << inFace.getId()
                               << " retransmit-retry-to=" << outFace.getId());
      }
    }
  }

  if (m_waitAndFwd) {
      int waitTime = m_waitTime * 1000;
      NFD_LOG_DEBUG(interest << " from=" << inFace.getId() << " noNextHop -- Retrying in " << waitTime << " ms");
      resultFormat resultsCopy;
      resultsCopy.nResultsToReturn = num_matches;
      for (int i = 0; i < num_matches; i++) {
        strcpy(resultsCopy.resultsArray[i].resultValue, m_forwarder.results.resultsArray[i].resultValue);
        NFD_LOG_DEBUG("Result " << i << " is " << m_forwarder.results.resultsArray[i].resultValue);
      }
      m_pendingInterests.push_back(interest);
      scheduler::schedule(time::milliseconds(waitTime), bind(&FuzzyStrategy::retrySendingInterest, this, ref(inFace), ref(interest), pitEntry, resultsCopy, -1));
      return;
  }

  NFD_LOG_DEBUG(interest << " from=" << inFace.getId() << " noNextHop");

  lp::NackHeader nackHeader;
  nackHeader.setReason(lp::NackReason::NO_ROUTE);
  this->sendNack(pitEntry, inFace, nackHeader);

  this->rejectPendingInterest(pitEntry);
}

void
FuzzyStrategy::afterReceiveNack(const Face& inFace, const lp::Nack& nack,
                                     const shared_ptr<pit::Entry>& pitEntry)
{
  this->processNack(inFace, nack, pitEntry);
}

void
FuzzyStrategy::beforeCSLookup(const Interest& interest, int& fuzzyMatches, bool waitAndFwd, float waitTime)
{
  NFD_LOG_DEBUG("beforeCSLookup interest name=" << interest.getName());
  strcpy(word, interest.getName().get(COMP_INDEX_FUZZY).toUri().c_str());
  // NFD_LOG_DEBUG("Fuzzy Matching for component " << word);
  num_matches = distance_no_open((void*)&m_forwarder.initStruct, word, (void*)&m_forwarder.results, THRESHOLD);
  fuzzyMatches = num_matches;
  m_waitAndFwd = waitAndFwd;
  m_waitTime = waitTime;
  // std::cerr << "Interest name " << interest.getName().toUri() << std::endl;
  // std::cerr << "Num_matches " << num_matches << std::endl;
  // for (int i = 0; i < num_matches; i++)
  //   std::cerr << "Fuzzy Prefix " << results.resultsArray[i].resultValue << std::endl;
}

void
FuzzyStrategy::retrySendingInterest(const Face& inFace, const Interest& interest,
                                    const shared_ptr<pit::Entry>& pitEntry, resultFormat resultsCopy,
                                    int matchIndex)
{
  shared_ptr<Interest> i = make_shared<Interest>(m_pendingInterests.front());

  NFD_LOG_DEBUG(*i << " Retrying fuzzy CS lookup");

  bool csHit = m_forwarder.doFuzzyCSLookup(inFace, *i, pitEntry, resultsCopy, matchIndex);

  if (!csHit) {
    if (matchIndex == -1) {
      NFD_LOG_DEBUG(*i << " Failed again fuzzy CS lookup");
      lp::NackHeader nackHeader;
      nackHeader.setReason(lp::NackReason::NO_ROUTE);
      this->sendNack(pitEntry, inFace, nackHeader);

      this->rejectPendingInterest(pitEntry);
    }
    else {
      NFD_LOG_DEBUG(*i << " Failed fuzzy CS lookup, sending initial match out");
      shared_ptr<Name> fuzzyName = make_shared<Name>(i->getName().getPrefix(COMP_INDEX_FUZZY));
      fuzzyName->append(resultsCopy.resultsArray[matchIndex].resultValue);
      for (int j = COMP_INDEX_FUZZY + 1; j < i->getName().size(); j++) {
        fuzzyName->append(i->getName().get(j));
      }
      NFD_LOG_DEBUG("Fuzzy Matching for name " << *fuzzyName);
      const fib::Entry& fibEntry = this->lookupFib(*pitEntry, fuzzyName);
      const fib::NextHopList& nexthops = fibEntry.getNextHops();
      fib::NextHopList::const_iterator it = nexthops.end();

      it = std::find_if(nexthops.begin(), nexthops.end(),
        bind(&isNextHopEligible, cref(inFace), *i, _1, pitEntry,
             false, time::steady_clock::TimePoint::min()));

      Face& outFace = it->getFace();
      Delegation del;
      del.name = Name(*fuzzyName);
      del.preference = 1;
      DelegationList list({del});
      const_cast<Interest&>(*i).setForwardingHint(list);
      this->sendInterest(pitEntry, outFace, *i);
      NFD_LOG_DEBUG(*i << " from=" << inFace.getId()
                             << " newPitEntry-to=" << outFace.getId());
    }
  }
  else {
    NFD_LOG_DEBUG(*i << " Found match after fuzzy CS lookup");
  }
  pendingInterestIndex++;
  m_pendingInterests.erase(m_pendingInterests.begin());
}

} // namespace fw
} // namespace nfd
