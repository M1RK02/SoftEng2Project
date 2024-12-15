sig Student {
	university: one University,
	applications: set Internship,
	interviews: set Internship,
	acceptedInternships: set Internship,
	recommendations: set Recommendation,
}

sig Company {
	internships: set Internship,
	recommendations: set Recommendation
}

sig University {
	monitoredInternships: set Internship,
	complaints: set Complaint
}

sig Internship {
	publishedBy: one Company,
	applicantsST: set Student,
	interviewedST: set Student,
	selectedST: set Student,
	recommendations: set Recommendation,
	monitoredBy:  set University,
	status: one Status,
	feedback: set Feedback
}

sig Recommendation {
	student: one Student,
	internship: one Internship,
	score: Int
}

abstract sig Feedback {
	relatedTo: one Internship
}

sig StudentFeedback extends Feedback {
	providedByST: one Student
}

sig CompanyFeedback extends Feedback {
	providedByCP: one Company
}

abstract sig Complaint {
	relatedTo: Internship,
	handledBy: University
}

sig StudentComplaint extends Complaint {
	filedByST: one Student
}

sig CompanyComplaint extends Complaint {
	filedByCP: one Company
}

enum Status { available, interviews, ongoing, closed }




----------------------------------------------------------------
-- FACTS
----------------------------------------------------------------


-- The student university must be valid
-- All the applications, inteviews and acceptedInternship must be of valid internship
-- The set of ST interviews is a subset of the ST applications
-- The set of ST acceptedInternship is a subset of the ST interviews
-- The university of the Student must be in the set of University that monitors the internship
fact StudentConstraints1 {
	all s: Student |
		s.university in University
		and s.applications in Internship
		and (s.interviews in Internship 
			and ( s.interviews in s.applications 
				or #s.interviews = 0 ) )
		and (s.acceptedInternships in Internship
			and ( s.acceptedInternships in s.interviews 
				or #s.acceptedInternships = 0 )
			and ( s.acceptedInternships in s.applications 
				or #s.acceptedInternships = 0 ) )
		and ( #s.acceptedInternships > 0 
				implies s.university in s.acceptedInternships.monitoredBy )
}


-- A student can't be in two different ongoing internships at the same time
fact StudentConstraints2 {
	no s: Student, disj i1, i2: Internship |
	i1 in s.acceptedInternships
	and
	i2 in s.acceptedInternships
	and
	i1.status = ongoing and i2.status = ongoing
}


-- A Company can only provide feedbacks on its own internships
fact CompanyConstraints {
	all i: Internship, f: i.feedback|
		f.relatedTo = i 
		and
		( f.providedByCP in i.publishedBy )
}

-- A Student can only provide feedbacks on its accepted internships
fact StudentFeedbacks {
	all i: Internship, f: i.feedback|
		f.relatedTo = i 
		and
		( f.providedByST in i.selectedST )
}


-- An internship in status available can only have applicantsST
fact InternshipConstraints1 {
	all i: Internship |
		i.status = available implies ( #i.applicantsST >= 0 
							and #i.interviewedST = 0 
							and #i.selectedST = 0 
							and #i.feedback = 0 )
}

-- An internship in status interviews has at least 
-- 1 Student in interviewedST and no Students in selectedST
fact InternshipConstraints2 {
	all i: Internship |
		i.status = interviews implies ( #i.applicantsST > 0 
							and #i.interviewedST > 0
							and #i.selectedST = 0 
							and #i.feedback = 0 )
}

-- An internship in status ongoing has at least 
-- 1 Student in selectedST and no Feedbacks
fact InternshipConstraints3 {
	all i: Internship |
			i.status = ongoing implies ( #i.applicantsST > 0 
				and #i.interviewedST > 0 
				and #i.selectedST > 0
				and #i.feedback = 0 )
}

-- An internship in status closed has 2 Feedback
-- one from ST and one from CP
fact InternshipConstraints4 {
	all i: Internship |
		i.status = closed implies ( #i.applicantsST > 0 
							and #i.interviewedST > 0 
							and #i.selectedST > 0 
							and #i.feedback = 2)
}


-- If an internship has feedback is in status closed
fact FeedbackConstraints {
	all f: Feedback |
		f.relatedTo.status = closed
}

-- If an internship has complaints is either in status ongoing or closed
fact ComplaintConstraints {
	all c: Complaint |
		c.relatedTo.status = ongoing 
		or c.relatedTo.status = closed
}

-- Complaints filed by a students must be handled by his university
fact STComplaintConstraints {
	all sc: StudentComplaint |
		sc.handledBy = sc.filedByST.university
}

-- All recommendations scores must be between 0 and 100
fact ValidRecommendations {
    all r: Recommendation | r.score > 0 and r.score <= 100
}

-- A student can file only one complaint 
-- about the same internship
fact OnlyOneComplaintPerST {
	no disj c1, c2: Complaint |
		c1.relatedTo = c2.relatedTo
		and
		c1.filedByST = c2.filedByST
}

-- A student can provide only one feedback 
-- about the same internship
fact OnlyOneFeedbackPerST {
	no disj f1, f2: Feedback |
		f1.relatedTo = f2.relatedTo
		and
		f1.providedByST = f2.providedByST
}

-- A company can provide only one feedback 
-- about the same internship
fact OnlyOneFeedbackPerCP {
	no disj f1, f2: Feedback |
		f1.relatedTo = f2.relatedTo
		and
		f1.providedByCP = f2.providedByCP
}

-- There cannot be two recommendations related 
-- to the same student and same internship
fact UniqueRecommendations1 {
	no disj r1, r2: Recommendation |
	r1.student = r2.student
	and
	r1.internship = r2.internship
}

-- Every recommendation is unique
fact UniqueRecommendations2 {
	all disj c1, c2: Company |
		(c1.recommendations & c2.recommendations = none)
}

-- The universities of the selected ST
-- must be in the Internship.monitoredBy relation
fact InternshipMonitoredByUniv {
	all i: Internship |
		i.selectedST.university in i.monitoredBy
}


-- There can't be lone universities
fact NoUniversityWithoutST {
	no u: University | not u in Student.university
}


------------ Bidirectional Facts ------------

-- All feedbacks are related to an internship
fact InternshipsRelatedToFeedbacks {
	all i: Internship, f: Feedback |
		f in i.feedback iff f.relatedTo = i
}

-- An internship is in the list of company internships
-- iff its published by them
fact InternshipPublishedByCompany {
	all i: Internship, c: Company |
		i in c.internships iff c in i.publishedBy 
}

-- The relation between University and Internships is bidirectional
fact UniversityConstraints1 {
	all u: University, i: Internship |
		i in u.monitoredInternships iff u in i.monitoredBy
}

-- The relation between University and Complaint is bidirectional
fact UniversityConstraints2 { 
	all u: University, c: Complaint |
	c in u.complaints iff u in c.handledBy
}

-- A complaint filed By a company about an internship
-- must be handled by a university in the universities
-- of the selected Students
fact ComplaintHandledByRightUniversity {
	all c: CompanyComplaint |
		c.handledBy in c.relatedTo.selectedST.university
}

-- The relations between Recommendation and Student is bidirectional
fact BidirRecommendationsConstraints1 {
	all r: Recommendation, s: Student |
		s in r.student iff r in s.recommendations
}

-- The relations between Recommendation and Internship is bidirectional
fact BidirRecommendationsConstraints2 {
	all r: Recommendation, i: Internship |
		i in r.internship iff r in i.recommendations
}

-- The relation between Student.applications 
-- and Internship.applicantsST is bidirectional
fact STBidirectionalConstraints1 {
	all s: Student, i: Internship |
		i in s.applications iff s in i.applicantsST
}

-- The relation between Student.interviews 
-- and Internship.interviewedST is bidirectional
fact STBidirectionalConstraints2 {
	all s: Student, i: Internship |
		i in s.interviews iff s in i.interviewedST
}

-- The relation between Student.acceptedInternships 
-- and Internship.selectedST is bidirectional
fact STBidirectionalConstraints3 {
	all s: Student, i: Internship |
		i in s.acceptedInternships iff s in i.selectedST
}





----------------------------------------------------------------
-- ASSERTIONS
----------------------------------------------------------------

assert SubsetAcceptedInterviewsApplications {
    all s: Student |
        s.acceptedInternships in s.interviews 
        and s.interviews in s.applications
}

check SubsetAcceptedInterviewsApplications for 10


assert FeedbackOnlyWhenClosed {
    all i: Internship |
        #i.feedback > 0 implies i.status = closed
}

check FeedbackOnlyWhenClosed for 10


assert ValidInternshipStates {
    all i: Internship |
        (i.status = available implies (#i.interviewedST = 0 and #i.selectedST = 0)) 
        and
        (i.status = interviews implies (#i.selectedST = 0 and #i.interviewedST > 0))
        and
        (i.status = ongoing implies (#i.selectedST > 0 and #i.feedback = 0))
        and
        (i.status = closed implies (#i.feedback = 2))
}

check ValidInternshipStates for 10


assert MonitoredInternshipsByUniversity {
    all s: Student, i: Internship | 
	i in s.acceptedInternships implies s.university in i.monitoredBy
}

check MonitoredInternshipsByUniversity for 10


assert UniqueFeedbackAndComplaints {
    no disj f1, f2: Feedback | f1.relatedTo = f2.relatedTo and f1 = f2
    and
    no disj c1, c2: Complaint | c1.relatedTo = c2.relatedTo and c1 = c2
}

check UniqueFeedbackAndComplaints for 10


assert FeedbackByPublishingCompany {
	all i: Internship |
		i.status = closed implies i.feedback.providedByCP = i.publishedBy
}

check FeedbackByPublishingCompany for 10


assert UniqueComplaintsByStudent {
    all s: Student |
        all i: Internship |
            lone c: Complaint | c.relatedTo = i and c.filedByST = s
}

check UniqueComplaintsByStudent for 10


assert UniqueFeedbackByStudent {
    all s: Student |
        all i: Internship |
            lone f: StudentFeedback | f.relatedTo = i and f.providedByST = s
}

check UniqueFeedbackByStudent for 10


assert NoDuplicateInternshipsForStudent {
    all s: Student | 
        no disj i1, i2: s.acceptedInternships | i1.status = ongoing and i2.status = ongoing
}

check NoDuplicateInternshipsForStudent for 10


----------------------------------------------------------------
-- PREDICATES
----------------------------------------------------------------

pred baseWorld {
	#Student = 1
	#Company = 1
	#University = 1
	#Internship = 1
	#Recommendation = 1
	#Complaint = 2
	one i: Internship | i.status = closed
}
run baseWorld for 10 but 8 Int

pred World1 {
	#Student > 1
	#Company > 1
	all c: Company | #c.internships > 0
	some i: Internship | i.status = available
	some i: Internship | i.status = ongoing
	some i: Internship | i.status = closed
	#University > 0
	some u: University| #u.complaints > 0
	#Recommendation > 0
}
run World1 for 10 but 8 Int

pred World2 {
	#Student > 4
	#Company > 2
	all c: Company | #c.internships > 0
	some i: Internship | i.status = available
	some i: Internship | i.status = interviews
	some i: Internship | i.status = ongoing
	some i: Internship | i.status = closed
	#University > 2
	some u: University| #u.complaints > 0
	#Recommendation > 0
}
run World2 for 10 but 8 Int



