abstract sig Bool {}
one sig True extends Bool {}
one sig False extends Bool {}

// Signatures
sig DateTimes{

}

abstract sig User {
  id: one Int,
}

sig Student, Educator extends User {}

sig StudentTeam {
  var students: set Student,
  battle: one Battle,
  var score: one Int
}

sig Tournament {
  id: one Int,
  registrationDeadline: one DateTimes,
  var battles: set Battle,
  var activeBattles: set Battle,
  var participants: set Student,
  owner: one Educator,
  var invitedEducators: set Educator,
  var isOpen: one Bool
}

sig Battle {
  id: one Int,
  owner: one Educator,
  registrationDeadline: one DateTimes,
  finalSubmissionDeadline: one DateTimes,
  minTeamSize: one Int,
  maxTeamSize: one Int,
  var participants: set StudentTeam,
  codeKata: one CodeKata,
  githubRepoSubmissions: lone GitHubRepoSubmission,
  githubRepoEvaluations: lone GitHubRepoEvaluation,
  tournament: one Tournament,
  var isOpen: one Bool
}

sig CodeKata {
  testCases: set TestCase,
  buildAutomationScripts: set BuildAutomationScript,
  battle: one Battle
}

sig GitHubRepo {
  url: one String
}

sig GitHubRepoSubmission, GitHubRepoEvaluation extends GitHubRepo {}

sig TestCase {
  codeKata: one CodeKata
}

sig BuildAutomationScript {
    codeKata: one CodeKata
}

fact TournamentHasUniqueId {
    all t1: Tournament | t1.id > 0
}

fact BattleHasUniqueId {
    all b1: Battle | b1.id > 0
}

fact UserHasUniqueId {
    all s1: User | s1.id > 0
}

fact TournamentHasUniqueId {
    all t1, t2: Tournament | t1 != t2 implies t1.id != t2.id
}

fact BattleHasUniqueId {
    all b1, b2: Battle | b1 != b2 implies b1.id != b2.id
}

fact UserHasUniqueId {
    all s1, s2: User | s1 != s2 implies s1.id != s2.id
}

fact OneTeamPerStudentPerBattle {
    all s: Student, b: Battle | lone t: StudentTeam | isInTeamForBattle[s, t, b]
}

fact StudentTeamAbidesByBattleSizeConditions {
    all st: StudentTeam | st.battle.minTeamSize <= #st.students and #st.students <=  st.battle.maxTeamSize
}

fact TournamentActiveBattlesInTournamentBattles{
    all t: Tournament | t.activeBattles in t.battles 
}

fact NumberOfActiveBattlesOfTournamentIsEqualToNumberOfOpenBattles{
    all t: Tournament | #t.activeBattles = #{b: t.battles | b.isOpen = True}
}

fact BattleInOnlyOneTournament{
    all t1, t2: Tournament | disj[t1.battles, t2.battles]
}

fact TournamentWithActiveBattlesCannotBeClosed{
    all t: Tournament | #t.activeBattles > 0 implies t.isOpen = True
}

pred isStudent[user: User] {
    user in Student
}

pred isEducator[user: User] {
    user in Educator
}
pred isTournamentOwner[e: Educator, t: Tournament] {
    e = t.owner
}

pred isPartOfTournament[e: Educator, t: Tournament] {
    e in t.invitedEducators
}

pred isBattleOwner[e: Educator, b: Battle] {
    e = b.owner
}

pred isInTournament[s: Student, t: Tournament] {
    s in t.participants
}

pred isInBattle[s: Student, b: Battle] {
    one st: StudentTeam | st.battle = b and s in st.students
}

pred isInTeamForBattle[s: Student, st: StudentTeam, b: Battle] {
    s in st.students and st.battle = b
}

pred example{
   some s: Student, st: StudentTeam | s in st.students
}

fun getTournamentBattles[t: Tournament]: set Battle {
    t.battles
}

fun getBattlesOfStudent[s: Student]: set Battle {
    { b: Battle | isInBattle[s, b] }
}

assert oneTeamPerStudentPerBattle {
    all s: Student, b: Battle | lone t: StudentTeam | isInTeamForBattle[s, t, b]
}

assert StudentRegisteredToTournamentOfBattleTheyAreRegisteredTo  {
    all s: Student, t: Tournament, b: Battle, st: StudentTeam| 
        st in b.participants and b in t.battles implies s in t.participants
}


check oneTeamPerStudentPerBattle
check StudentRegisteredToTournamentOfBattleTheyAreRegisteredTo


run example
