include "../../Protocol/SHT/Configuration.i.dfy"
include "Parameters.i.dfy"
include "../Common/GenericRefinement.i.dfy"
include "../Common/NodeIdentity.i.dfy"

module SHT__CConfiguration_i {
import opened SHT__Configuration_i
import opened Impl_Parameters_i
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened GenericRefinement_i
import opened Common__NodeIdentity_i
import opened Common__SeqIsUniqueDef_i

/************************** AutoMan Translation ************************/
datatype CSHTConfiguration = 
CSHTConfiguration(
    // clientIds: seq<EndPoint>, 
    hostIds: seq<EndPoint>, 
    rootIdentity: EndPoint, 
    params: CParameters
)

predicate CSHTConfigurationIsValid(s: CSHTConfiguration) 
{
    CSHTConfigurationIsAbstractable(s) 
    // && 
    // (forall i :: i in s.clientIds ==> EndPointIsValid(i)) 
    && 
    (forall i :: i in s.hostIds ==> EndPointIsValid(i)) 
    && 
    EndPointIsValid(s.rootIdentity) 
    && 
    CParametersIsValid(s.params)
    /** Manually Added */
    && SeqIsUnique(s.hostIds)
}

predicate CSHTConfigurationIsAbstractable(s: CSHTConfiguration) 
{
    // (forall i :: i in s.clientIds ==> EndPointIsAbstractable(i)) 
    && 
    (forall i :: i in s.hostIds ==> EndPointIsAbstractable(i)) 
    && 
    EndPointIsAbstractable(s.rootIdentity) 
    && 
    CParametersIsAbstractable(s.params)
}

function AbstractifyCSHTConfigurationToSHTConfiguration(s: CSHTConfiguration) : SHTConfiguration 
    requires CSHTConfigurationIsAbstractable(s)
{
    SHTConfiguration([], AbstractifySeq(s.hostIds, AbstractifyEndPointToNodeIdentity), AbstractifyEndPointToNodeIdentity(s.rootIdentity), AbstractifyCParametersToParameters(s.params))
    // SHTConfiguration(AbstractifySeq(s.clientIds, AbstractifyEndPointToNodeIdentity), AbstractifySeq(s.hostIds, AbstractifyEndPointToNodeIdentity), AbstractifyEndPointToNodeIdentity(s.rootIdentity), AbstractifyCParametersToParameters(s.params))
}

function method CHostsDistinct(hostIds: seq<EndPoint>, i: int, j: int) : bool 
    requires (forall i :: i in hostIds ==> EndPointIsValid(i))
    ensures CHostsDistinct(hostIds, i, j) == HostsDistinct(AbstractifySeq(hostIds, AbstractifyEndPointToNodeIdentity), i, j)
{
    0 <= i && i < |hostIds| && 0 <= j && j < |hostIds| && hostIds[i] == hostIds[j] ==> i == j
}
/************************** AutoMan Translation End ************************/
// datatype CSHTConfiguration = CSHTConfiguration(
//     // clientIds : seq<EndPoint>,
//     hostIds : seq<EndPoint>,
//     rootIdentity : EndPoint,
//     params : CParameters
// )

// predicate CSHTConfigurationIsAbstractable(c:CSHTConfiguration){
//     && SeqIsAbstractable(c.hostIds, AbstractifyEndPointToNodeIdentity)
//     && EndPointIsAbstractable(c.rootIdentity)
//     && CParametersIsAbstractable(c.params)
//     // && SeqIsUnique(c.hostIds)
// }   

// predicate CSHTConfigurationIsValid(c:CSHTConfiguration){
//     && SeqIsValid(c.hostIds, EndPointIsValid)
//     && EndPointIsValid(c.rootIdentity)
//     && CParametersIsValid(c.params)
//     && 0 < |c.hostIds|
//     && c.rootIdentity in c.hostIds
//     && (forall i, j :: HostsDistinct(c.hostIds, i, j))
//     && SeqIsUnique(c.hostIds)
// }   

// function AbstractifyCSHTConfigurationToConfiguration(config:CSHTConfiguration) : SHTConfiguration
//     requires CSHTConfigurationIsAbstractable(config)
// {
//     SHTConfiguration(
//         [],
//         AbstractifySeq(config.hostIds, AbstractifyEndPointToNodeIdentity),
//         AbstractifyEndPointToNodeIdentity(config.rootIdentity),
//         AbstractifyCParametersToParameters(config.params)
//     )
// }

// predicate method HostsDistinct(hostIds:seq<EndPoint>, i:int, j:int)
//     requires SeqIsValid(hostIds, EndPointIsValid)
// {
//     0 <= i < |hostIds| && 0 <= j < |hostIds| && hostIds[i] == hostIds[j] ==> i == j
// }


lemma lemma_WFSHTConcreteConfiguration(config:CSHTConfiguration)
    ensures CSHTConfigurationIsValid(config)
    && 0 < |config.hostIds|
    && config.rootIdentity in config.hostIds
    ==> CSHTConfigurationIsAbstractable(config)
        && WFSHTConfiguration(AbstractifyCSHTConfigurationToSHTConfiguration(config));
{
    if (CSHTConfigurationIsValid(config)
        && 0 < |config.hostIds|)
    {
        //lemma_CardinalityNonEmpty(config.hostIds);
        assert SeqIsValid(config.hostIds, EndPointIsValid);
        assert forall i :: 0 <= i < |config.hostIds| ==> EndPointIsValid(config.hostIds[i]);
        var e := config.hostIds[0];
        assert AbstractifyEndPointToNodeIdentity(e) in AbstractifyCSHTConfigurationToSHTConfiguration(config).hostIds;
        assert 0 < |AbstractifyCSHTConfigurationToSHTConfiguration(config).hostIds|;
        var r_hostIds := AbstractifyCSHTConfigurationToSHTConfiguration(config).hostIds;
        assert SeqIsAbstractable(config.hostIds, AbstractifyEndPointToNodeIdentity);
        assert forall i, j :: 0 <= i < |r_hostIds| && 0 <= j < |r_hostIds| ==> EndPointIsAbstractable(config.hostIds[i]) && EndPointIsAbstractable(config.hostIds[j]);
        forall i, j | 0 <= i < |r_hostIds| && 0 <= j < |r_hostIds|
            ensures r_hostIds[i] == r_hostIds[j] ==> i == j;
        {
            if r_hostIds[i] == r_hostIds[j] {
                if i != j {
                    assert r_hostIds[i] == AbstractifyEndPointToNodeIdentity(config.hostIds[i]);
                    assert r_hostIds[j] == AbstractifyEndPointToNodeIdentity(config.hostIds[j]);
                    lemma_AbstractifyEndPointToNodeIdentity_injective(config.hostIds[i], config.hostIds[j]);
                    // assert config.hostIds[i] == config.hostIds[j] ==> i == j;
                    assert AbstractifyEndPointToNodeIdentity(config.hostIds[i]) == AbstractifyEndPointToNodeIdentity(config.hostIds[j]) ==> config.hostIds[i] == config.hostIds[j];
                    assert config.hostIds[i] == config.hostIds[j];
                    reveal_SeqIsUnique();
                    assert i == j;
                    assert false;
                }
            }

        }
    }
}

}