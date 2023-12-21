// Signatures
abstract sig User {
  id: one Int,
  name: one String,
  email: one String,
  githubAccount: one String,
  password: one String
}

sig Student, Educator extends User {}

sig StudentTeam {
  students: set Student
}

sig Tournament {
  id: one Int,
  name: one String,
  registrationDeadline: one Time,
  battles: set Battle,
  participants: set Student,
  owner: one Educator,
  invitedEducators: set Educator
}

sig Battle {
  id: one Int,
  owner: one Educator,
  registrationDeadline: one Time,
  finalSubmissionDeadline: one Time,
  minParticipants: one Int,
  maxParticipants: one Int,
  participants: set StudentTeam,
  codeKata: one CodeKata,
  githubRepoSubmissions: lone GitHubRepoSubmission,
  githubRepoEvaluations: lone GitHubRepoEvaluation,
  tournament: one Tournament
}

sig CodeKata {
  language: one String,
  description: one String,
  testCases: set TestCase,
  buildAutomationScripts: set BuildAutomationScript
}

sig GitHubRepo {
  url: one String
}

sig GitHubRepoSubmission, GitHubRepoEvaluation extends GitHubRepo {}

sig TestCase {
}

sig BuildAutomationScript {
}

// Relations
fact ValidPasswords {
  all u: User | u.password.length >= 8
}

fact CanOwnBattlesInTournamentIfOwnsTournamentOrParticipatesInTournament{
  all e: Educator, t: Tournament, b: Battle | b.owner = e and b.tournament = t implies (b in t.invitedEducators or b = t.owner)
}

// Use Case 4: Educator Creates Tournament
pred CreateTournament[e: Educator, registrationDeadline: Time, name: String] {
  let newTournament = Tournament & {
    id: #Tournament + 1,
    registrationDeadline: registrationDeadline,
    battles: none,
    participants: none,
    owner: e,
    invitedEducators: none
  } 
}
pred CreateBattle[e: Educator, tournament: Tournament, registrationDeadline: Time, submissionDeadline: Time, minParticipants: Int, 
					maxParticipants: Int, language: String, description: String,
					testCases: set TestCase,   buildAutomationScripts: set BuildAutomationScript] {
  
let newCodeKata = CodeKata & {
  language: language,
  description: description,
  testCases: testCases,
  buildAutomationScripts: buildAutomationScripts
}
let newBattle= Battle & {
    id: #Battle + 1
    owner: e
    registrationDeadline: registrationDeadline,
    finalSubmissionDeadline: one Time,
    minParticipants: minParticipants,
    maxParticipants: maxParticipants,
    participants: none,
    codeKata: newCodeKata,
    githubRepoSubmissions: none,
    githubRepoEvaluations: none,
    tournament: tournament
  }  
}

// ... Additional use case predicates can be added ...

// Assertions
assert AtLeastOneUser {
  some u: User | u in Student or u in Educator
}

assert EachBattleBelongsToTournament {
  all b: Battle | b in b.tournament.battles
}

run AtLeastOneUser for 5

// ... Additional assertions or run commands can be added ...
