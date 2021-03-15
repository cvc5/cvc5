; COMMAND-LINE: --strings-exp --produce-proofs --no-re-elim
; EXPECT: sat
(set-logic ALL)
(declare-const actionName String)
(declare-const actionNamespace String)
(declare-const resource_account String)
(declare-const resource_partition String)
(declare-const resource_prefix String)
(declare-const resource_region String)
(declare-const resource_resource String)
(declare-const resource_service String)

; Action: p0.0
(declare-const p0.0.action Bool)
(assert (= p0.0.action (or (and (= "lambda" actionNamespace) (= "invokefunction" actionName)) (and (= "lambda" actionNamespace) (= "listfunctions" actionName)) (and (= "logs" actionNamespace) (= "createloggroup" actionName)) (and (= "logs" actionNamespace) (= "createlogstream" actionName)) (and (= "logs" actionNamespace) (= "describeloggroups" actionName)) (and (= "logs" actionNamespace) (= "describelogstreams" actionName)) (and (= "logs" actionNamespace) (= "putlogevents" actionName)) (and (= "logs" actionNamespace) (= "getlogevents" actionName)) (and (= "logs" actionNamespace) (= "filterlogevents" actionName)))))

; Resource: p0.0
(declare-const p0.0.resource Bool)
(assert (= p0.0.resource (or (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "lambda" resource_service) (= "us-east-1" resource_region) (= "111122223333" resource_account) (str.prefixof "pvivjbql:" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "lambda" resource_service) (= "us-west-2" resource_region) (= "111122223333" resource_account) (str.prefixof "pvivjbql:" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "logs" resource_service) (= "" resource_region) (= "111122223333" resource_account) (str.prefixof "rrd-ytqjm:" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "logs" resource_service) (= "" resource_region) (= "111122223333" resource_account) (str.prefixof "rrd-ytqjm:" resource_resource) (str.contains (str.substr resource_resource 10 (- (str.len resource_resource) 10)) ":rrd-qkkjoe:")))))

; Statement: p0.0
(declare-const p0.0.statement.allow Bool)
(assert (= p0.0.statement.allow (and p0.0.action p0.0.resource)))

; Action: p0.1
(declare-const p0.1.action Bool)
(assert (= p0.1.action (or (and (= "states" actionNamespace) (= "describestatemachine" actionName)) (and (= "states" actionNamespace) (= "startexecution" actionName)) (and (= "states" actionNamespace) (= "deletestatemachine" actionName)) (and (= "states" actionNamespace) (= "listexecutions" actionName)) (and (= "states" actionNamespace) (= "updatestatemachine" actionName)) (and (= "states" actionNamespace) (= "describeexecution" actionName)) (and (= "states" actionNamespace) (= "describestatemachineforexecution" actionName)) (and (= "states" actionNamespace) (= "getexecutionhistory" actionName)) (and (= "states" actionNamespace) (= "stopexecution" actionName)))))

; Resource: p0.1
(declare-const p0.1.resource Bool)
(assert (= p0.1.resource (or (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "states" resource_service) (= "us-east-1" resource_region) (= "111122223333" resource_account) (str.prefixof "qebnvtpqvhdw:" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "states" resource_service) (= "us-west-2" resource_region) (= "111122223333" resource_account) (str.prefixof "qebnvtpqvhdw:" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "states" resource_service) (= "us-east-1" resource_region) (= "111122223333" resource_account) (str.prefixof "iirfzwang:" resource_resource) (str.contains (str.substr resource_resource 10 (- (str.len resource_resource) 10)) ":")) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "states" resource_service) (= "us-west-2" resource_region) (= "111122223333" resource_account) (str.prefixof "iirfzwang:" resource_resource) (str.contains (str.substr resource_resource 10 (- (str.len resource_resource) 10)) ":")))))

; Statement: p0.1
(declare-const p0.1.statement.allow Bool)
(assert (= p0.1.statement.allow (and p0.1.action p0.1.resource)))

; Action: p0.2
(declare-const p0.2.action Bool)
(assert (= p0.2.action (or (and (= "iam" actionNamespace) (= "getinstanceprofile" actionName)) (and (= "iam" actionNamespace) (= "getuser" actionName)) (and (= "iam" actionNamespace) (= "getrole" actionName)) (and (= "iam" actionNamespace) (= "passrole" actionName)) (and (= "sts" actionNamespace) (= "assumerole" actionName)) (and (= "sts" actionNamespace) (= "decodeauthorizationmessage" actionName)))))

; Resource: p0.2
(declare-const p0.2.resource Bool)
(assert (= p0.2.resource (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "iam" resource_service) (= "" resource_region) (= "111122223333" resource_account) (= "vpvt/yassqn-jmz-itxojjqzimtldywe-dmthtbzqhnrjiir" resource_resource))))

; Statement: p0.2
(declare-const p0.2.statement.allow Bool)
(assert (= p0.2.statement.allow (and p0.2.action p0.2.resource)))

; Action: p0.3
(declare-const p0.3.action Bool)
(assert (= p0.3.action (or (and (= "s3" actionNamespace) (= "getobject" actionName)) (and (= "s3" actionNamespace) (= "getobjectversion" actionName)) (and (= "s3" actionNamespace) (= "listallmybuckets" actionName)) (and (= "s3" actionNamespace) (= "putobject" actionName)) (and (= "s3" actionNamespace) (= "putobjectacl" actionName)) (and (= "s3" actionNamespace) (= "getobjectacl" actionName)))))

; Resource: p0.3
(declare-const p0.3.resource Bool)
(assert (= p0.3.resource (or (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-mtlararqiopumhxt-mgtp-us-crkr-1" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-mtlararqiopumhxt-mgtp-us-crkr-1/" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-mtlararqiopumhxt-mgtp-us-zfjo-2" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-mtlararqiopumhxt-mgtp-us-zfjo-2/" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "us-crkr-1.ivrvqmnmbxpkvwua" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "us-crkr-1.ivrvqmnmbxpkvwua/" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "us-zfjo-2.ivrvqmnmbxpkvwua" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "us-zfjo-2.ivrvqmnmbxpkvwua/" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-igfinprxnbuhdeucsr-mgtp" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-igfinprxnbuhdeucsr-mgtp/" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-igfinprxnbuhdeucsr-mgtp-zfjo" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-igfinprxnbuhdeucsr-mgtp-zfjo/" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-vrtpsbyipzmdhzvdeb-mgtp" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-vrtpsbyipzmdhzvdeb-mgtp/" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-vrtpsbyipzmdhzvdeb-mgtp-zfjo" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-vrtpsbyipzmdhzvdeb-mgtp-zfjo/" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-ftmvhop-oehokmeroq-mgtp-crkr" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-ftmvhop-oehokmeroq-mgtp-crkr/" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-ftmvhop-oehokmeroq-mgtp-zfjo" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-ftmvhop-oehokmeroq-mgtp-zfjo/" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "pso-mgtp-crkr-rkbp-6" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "pso-mgtp-crkr-rkbp-6/" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "pso-mgtp-zfjo-rkbp-6" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "pso-mgtp-zfjo-rkbp-6/" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "pso-mgtp-crkr-rkbp" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "pso-mgtp" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "pso-mgtp-crkr-rkbp" resource_resource) (str.contains resource_resource "/")))))

; Statement: p0.3
(declare-const p0.3.statement.allow Bool)
(assert (= p0.3.statement.allow (and p0.3.action p0.3.resource)))

; Action: p0.4
(declare-const p0.4.action Bool)
(assert (= p0.4.action (or (and (= "s3" actionNamespace) (= "getobject" actionName)) (and (= "s3" actionNamespace) (= "getobjectversion" actionName)) (and (= "s3" actionNamespace) (= "listallmybuckets" actionName)) (and (= "s3" actionNamespace) (= "listbucket" actionName)) (and (= "s3" actionNamespace) (= "putobject" actionName)) (and (= "s3" actionNamespace) (= "putobjectacl" actionName)) (and (= "s3" actionNamespace) (= "getobjectacl" actionName)))))

; Resource: p0.4
(declare-const p0.4.resource Bool)
(assert (= p0.4.resource (or (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-igfinprxnbuhdeucsr-mgtp" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-igfinprxnbuhdeucsr-mgtp/afo" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-igfinprxnbuhdeucsr-mgtp-zfjo" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-igfinprxnbuhdeucsr-mgtp-zfjo/afo" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-vrtpsbyipzmdhzvdeb-mgtp" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-vrtpsbyipzmdhzvdeb-mgtp/syv" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-vrtpsbyipzmdhzvdeb-mgtp-zfjo" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-vrtpsbyipzmdhzvdeb-mgtp-zfjo/syv" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-ftmvhop-oehokmeroq-mgtp-crkr" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-ftmvhop-oehokmeroq-mgtp-crkr/bohxlmimzpypgtruh" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (= "yom-rkbp-ftmvhop-oehokmeroq-mgtp-zfjo" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "s3" resource_service) (= "" resource_region) (= "" resource_account) (str.prefixof "yom-rkbp-ftmvhop-oehokmeroq-mgtp-zfjo/bohxlmimzpypgtruh" resource_resource)))))

; Statement: p0.4
(declare-const p0.4.statement.allow Bool)
(assert (= p0.4.statement.allow (and p0.4.action p0.4.resource)))

; Action: p0.5
(declare-const p0.5.action Bool)
(assert (= p0.5.action (or (and (= "logs" actionNamespace) (= "createexporttask" actionName)) (and (= "logs" actionNamespace) (= "cancelexporttask" actionName)))))

; Resource: p0.5
(declare-const p0.5.resource Bool)
(assert (= p0.5.resource (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "logs" resource_service) (= "" resource_region) (= "111122223333" resource_account) (str.prefixof "rrd-ytqjm:" resource_resource))))

; Statement: p0.5
(declare-const p0.5.statement.deny Bool)
(assert (= p0.5.statement.deny (and p0.5.action p0.5.resource)))

; Action: p0.6
(declare-const p0.6.action Bool)
(assert (= p0.6.action (and (= "events" actionNamespace) (= "putrule" actionName))))

; Resource: p0.6
(declare-const p0.6.resource Bool)
(assert (= p0.6.resource (or (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "events" resource_service) (= "us-east-1" resource_region) (= "111122223333" resource_account) (= "lbpi/mgtp-zyp-iumyz-bjbw" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "events" resource_service) (= "us-west-2" resource_region) (= "111122223333" resource_account) (= "lbpi/mgtp-zyp-iumyz-bjbw" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "events" resource_service) (= "us-east-1" resource_region) (= "111122223333" resource_account) (= "lbpi/mgtp-hddginvmfupkxnfbwnaxrfttnqn" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "events" resource_service) (= "us-west-2" resource_region) (= "111122223333" resource_account) (= "lbpi/mgtp-hddginvmfupkxnfbwnaxrfttnqn" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "events" resource_service) (= "us-east-1" resource_region) (= "111122223333" resource_account) (= "lbpi/mgtp-bwazegmezgmxgctctsgoamt" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "events" resource_service) (= "us-west-2" resource_region) (= "111122223333" resource_account) (= "lbpi/mgtp-bwazegmezgmxgctctsgoamt" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "events" resource_service) (= "us-east-1" resource_region) (= "111122223333" resource_account) (= "lbpi/mgtp-hujvnbavuj-iumyz-bjbw" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "events" resource_service) (= "us-east-1" resource_region) (= "111122223333" resource_account) (= "lbpi/mgtp-ivbbcudzyzmjoalqqx-iumyz-bjbw" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "events" resource_service) (= "us-east-1" resource_region) (= "111122223333" resource_account) (= "lbpi/mgtp-sippdrhzzwz-iumyz-bjbw" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "events" resource_service) (= "us-west-2" resource_region) (= "111122223333" resource_account) (= "lbpi/mgtp-hujvnbavuj-iumyz-bjbw" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "events" resource_service) (= "us-west-2" resource_region) (= "111122223333" resource_account) (= "lbpi/mgtp-ivbbcudzyzmjoalqqx-iumyz-bjbw" resource_resource)) (and (= "arn" resource_prefix) (= "aws" resource_partition) (= "events" resource_service) (= "us-west-2" resource_region) (= "111122223333" resource_account) (= "lbpi/mgtp-sippdrhzzwz-iumyz-bjbw" resource_resource)))))

; Statement: p0.6
(declare-const p0.6.statement.allow Bool)
(assert (= p0.6.statement.allow (and p0.6.action p0.6.resource)))

; Policy: 0
(declare-const p0.denies Bool)
(assert (= p0.denies p0.5.statement.deny))
(declare-const p0.allows Bool)
(assert (= p0.allows (and (not p0.5.statement.deny) (or p0.0.statement.allow p0.1.statement.allow p0.2.statement.allow p0.3.statement.allow p0.4.statement.allow p0.6.statement.allow))))
(declare-const p0.neutral Bool)
(assert (= p0.neutral (and (not p0.allows) (not p0.5.statement.deny))))

; Action: p1.1
(declare-const p1.1.action Bool)
(assert (= p1.1.action (or (and (= "s3" actionNamespace) (= "putbucketacl" actionName)) (and (= "s3" actionNamespace) (= "putbucketpolicy" actionName)) (and (= "s3" actionNamespace) (= "deletebucketpolicy" actionName)))))

; Action: p1.2
(declare-const p1.2.action Bool)
(assert (= p1.2.action (or (and (= "s3" actionNamespace) (= "objectowneroverridetobucketowner" actionName)) (and (= "s3" actionNamespace) (= "putobjectversionacl" actionName)) (and (= "s3" actionNamespace) (= "putobjectacl" actionName)))))

; Action: p1.3
(declare-const p1.3.action Bool)
(assert (= p1.3.action (or (and (= "sqs" actionNamespace) (= "removepermission" actionName)) (and (= "sqs" actionNamespace) (= "addpermission" actionName)))))

; Action: p1.4
(declare-const p1.4.action Bool)
(assert (= p1.4.action (or (and (= "sns" actionNamespace) (= "addpermission" actionName)) (and (= "sns" actionNamespace) (= "removepermission" actionName)))))

; Action: p1.5
(declare-const p1.5.action Bool)
(assert (= p1.5.action (or (and (= "lambda" actionNamespace) (= "addpermission" actionName)) (and (= "lambda" actionNamespace) (= "removepermission" actionName)) (and (= "lambda" actionNamespace) (= "enablereplication" actionName)))))

; Action: p1.6
(declare-const p1.6.action Bool)
(assert (= p1.6.action (or (and (= "kms" actionNamespace) (= "putkeypolicy" actionName)) (and (= "kms" actionNamespace) (= "revokegrant" actionName)) (and (= "kms" actionNamespace) (= "creategrant" actionName)) (and (= "kms" actionNamespace) (= "retiregrant" actionName)))))

; Action: p1.7
(declare-const p1.7.action Bool)
(assert (= p1.7.action (or (and (= "sns" actionNamespace) (= "addpermission" actionName)) (and (= "sns" actionNamespace) (= "removepermission" actionName)))))

; Action: p1.8
(declare-const p1.8.action Bool)
(assert (= p1.8.action (and (= "rds" actionNamespace) (= "authorizedbsecuritygroupin_ress" actionName))))

; Action: p1.9
(declare-const p1.9.action Bool)
(assert (= p1.9.action (and (= "cloudformation" actionNamespace) (= "setstackpolicy" actionName))))

; Action: p1.10
(declare-const p1.10.action Bool)
(assert (= p1.10.action (or (and (= "iam" actionNamespace) (= "updateassumerolepolicy" actionName)) (and (= "iam" actionNamespace) (= "deactivatemfadevice" actionName)) (and (= "iam" actionNamespace) (= "createservicespecificcredential" actionName)) (and (= "iam" actionNamespace) (= "deleteaccesskey" actionName)) (and (= "iam" actionNamespace) (= "deletegroup" actionName)) (and (= "iam" actionNamespace) (= "updateopenidconnectproviderthumbprint" actionName)) (and (= "iam" actionNamespace) (= "removerolefrominstanceprofile" actionName)) (and (= "iam" actionNamespace) (= "updategroup" actionName)) (and (= "iam" actionNamespace) (= "createrole" actionName)) (and (= "iam" actionNamespace) (= "attachrolepolicy" actionName)) (and (= "iam" actionNamespace) (= "putrolepolicy" actionName)) (and (= "iam" actionNamespace) (= "addroletoinstanceprofile" actionName)) (and (= "iam" actionNamespace) (= "createloginprofile" actionName)) (and (= "iam" actionNamespace) (= "detachrolepolicy" actionName)) (and (= "iam" actionNamespace) (= "createaccountalias" actionName)) (and (= "iam" actionNamespace) (= "deleteservercertificate" actionName)) (and (= "iam" actionNamespace) (= "uploadsshpublickey" actionName)) (and (= "iam" actionNamespace) (= "detachgrouppolicy" actionName)) (and (= "iam" actionNamespace) (= "detachuserpolicy" actionName)) (and (= "iam" actionNamespace) (= "deleteopenidconnectprovider" actionName)) (and (= "iam" actionNamespace) (= "changepassword" actionName)) (and (= "iam" actionNamespace) (= "putgrouppolicy" actionName)) (and (= "iam" actionNamespace) (= "updateloginprofile" actionName)) (and (= "iam" actionNamespace) (= "updateservicespecificcredential" actionName)) (and (= "iam" actionNamespace) (= "creategroup" actionName)) (and (= "iam" actionNamespace) (= "removeclientidfromopenidconnectprovider" actionName)) (and (= "iam" actionNamespace) (= "updateuser" actionName)) (and (= "iam" actionNamespace) (= "deleteuserpolicy" actionName)) (and (= "iam" actionNamespace) (= "attachuserpolicy" actionName)) (and (= "iam" actionNamespace) (= "deleterole" actionName)) (and (= "iam" actionNamespace) (= "updateroledescription" actionName)) (and (= "iam" actionNamespace) (= "updateaccesskey" actionName)) (and (= "iam" actionNamespace) (= "updatesshpublickey" actionName)) (and (= "iam" actionNamespace) (= "updateservercertificate" actionName)) (and (= "iam" actionNamespace) (= "deletesigningcertificate" actionName)) (and (= "iam" actionNamespace) (= "updateaccountpasswordpolicy" actionName)) (and (= "iam" actionNamespace) (= "deleteservicelinkedrole" actionName)) (and (= "iam" actionNamespace) (= "createinstanceprofile" actionName)) (and (= "iam" actionNamespace) (= "resetservicespecificcredential" actionName)) (and (= "iam" actionNamespace) (= "deletepolicy" actionName)) (and (= "iam" actionNamespace) (= "deletesshpublickey" actionName)) (and (= "iam" actionNamespace) (= "createvirtualmfadevice" actionName)) (and (= "iam" actionNamespace) (= "createsamlprovider" actionName)) (and (= "iam" actionNamespace) (= "createuser" actionName)) (and (= "iam" actionNamespace) (= "createaccesskey" actionName)) (and (= "iam" actionNamespace) (= "passrole" actionName)) (and (= "iam" actionNamespace) (= "addusertogroup" actionName)) (and (= "iam" actionNamespace) (= "removeuserfromgroup" actionName)) (and (= "iam" actionNamespace) (= "deleterolepolicy" actionName)) (and (= "iam" actionNamespace) (= "enablemfadevice" actionName)) (and (= "iam" actionNamespace) (= "resyncmfadevice" actionName)) (and (= "iam" actionNamespace) (= "deleteaccountalias" actionName)) (and (= "iam" actionNamespace) (= "createpolicyversion" actionName)) (and (= "iam" actionNamespace) (= "updatesamlprovider" actionName)) (and (= "iam" actionNamespace) (= "deleteloginprofile" actionName)) (and (= "iam" actionNamespace) (= "deleteinstanceprofile" actionName)) (and (= "iam" actionNamespace) (= "uploadsigningcertificate" actionName)) (and (= "iam" actionNamespace) (= "deleteaccountpasswordpolicy" actionName)) (and (= "iam" actionNamespace) (= "deleteuser" actionName)) (and (= "iam" actionNamespace) (= "createopenidconnectprovider" actionName)) (and (= "iam" actionNamespace) (= "uploadservercertificate" actionName)) (and (= "iam" actionNamespace) (= "createpolicy" actionName)) (and (= "iam" actionNamespace) (= "createservicelinkedrole" actionName)) (and (= "iam" actionNamespace) (= "deletevirtualmfadevice" actionName)) (and (= "iam" actionNamespace) (= "attachgrouppolicy" actionName)) (and (= "iam" actionNamespace) (= "putuserpolicy" actionName)) (and (= "iam" actionNamespace) (= "updatesigningcertificate" actionName)) (and (= "iam" actionNamespace) (= "deletegrouppolicy" actionName)) (and (= "iam" actionNamespace) (= "addclientidtoopenidconnectprovider" actionName)) (and (= "iam" actionNamespace) (= "deleteservicespecificcredential" actionName)) (and (= "iam" actionNamespace) (= "deletepolicyversion" actionName)) (and (= "iam" actionNamespace) (= "setdefaultpolicyversion" actionName)) (and (= "iam" actionNamespace) (= "deletesamlprovider" actionName)))))

; Action: p1.11
(declare-const p1.11.action Bool)
(assert (= p1.11.action (or (and (= "glacier" actionNamespace) (= "setdataretrievalpolicy" actionName)) (and (= "glacier" actionNamespace) (= "abortvaultlock" actionName)) (and (= "glacier" actionNamespace) (= "initiatevaultlock" actionName)) (and (= "glacier" actionNamespace) (= "deletevaultaccesspolicy" actionName)) (and (= "glacier" actionNamespace) (= "completevaultlock" actionName)) (and (= "glacier" actionNamespace) (= "setvaultaccesspolicy" actionName)))))

; Action: p1.12
(declare-const p1.12.action Bool)
(assert (= p1.12.action (or (and (= "ses" actionNamespace) (= "putidentitypolicy" actionName)) (and (= "ses" actionNamespace) (= "deleteidentitypolicy" actionName)))))

; Action: p1.13
(declare-const p1.13.action Bool)
(assert (= p1.13.action (or (and (= "servicecatalog" actionNamespace) (= "deleteportfolioshare" actionName)) (and (= "servicecatalog" actionNamespace) (= "createportfolioshare" actionName)))))

; Action: p1.14
(declare-const p1.14.action Bool)
(assert (= p1.14.action (or (and (= "waf" actionNamespace) (= "deletewebacl" actionName)) (and (= "waf" actionNamespace) (= "updatewebacl" actionName)) (and (= "waf" actionNamespace) (= "createwebacl" actionName)))))

; Action: p1.15
(declare-const p1.15.action Bool)
(assert (= p1.15.action (or (and (= "waf-regional" actionNamespace) (= "deletewebacl" actionName)) (and (= "waf-regional" actionNamespace) (= "updatewebacl" actionName)) (and (= "waf-regional" actionNamespace) (= "createwebacl" actionName)))))

; Action: p1.16
(declare-const p1.16.action Bool)
(assert (= p1.16.action (or (and (= "acm" actionNamespace) (= "deletecertificate" actionName)) (and (= "acm" actionNamespace) (= "resendvalidationemail" actionName)))))

; Action: p1.17
(declare-const p1.17.action Bool)
(assert (= p1.17.action (and (= "cloudsearch" actionNamespace) (= "updateserviceaccesspolicies" actionName))))

; Action: p1.18
(declare-const p1.18.action Bool)
(assert (= p1.18.action (or (and (= "codestar" actionNamespace) (= "associateteammember" actionName)) (and (= "codestar" actionNamespace) (= "createproject" actionName)) (and (= "codestar" actionNamespace) (= "deleteproject" actionName)) (and (= "codestar" actionNamespace) (= "disassociateteammember" actionName)) (and (= "codestar" actionNamespace) (= "updateteammember" actionName)))))

; Action: p1.19
(declare-const p1.19.action Bool)
(assert (= p1.19.action (and (= "diode" actionNamespace) (= "updateaccountmappingrolearn" actionName))))

; Action: p1.20
(declare-const p1.20.action Bool)
(assert (= p1.20.action (and (= "greengrass" actionNamespace) (= "associateserviceroletoaccount" actionName))))

; Action: p1.21
(declare-const p1.21.action Bool)
(assert (= p1.21.action (or (and (= "iot" actionNamespace) (= "attachpolicy" actionName)) (and (= "iot" actionNamespace) (= "attachprincipalpolicy" actionName)) (and (= "iot" actionNamespace) (= "detachpolicy" actionName)) (and (= "iot" actionNamespace) (= "detachprincipalpolicy" actionName)) (and (= "iot" actionNamespace) (= "setdefaultauthorizer" actionName)) (and (= "iot" actionNamespace) (= "setdefaultpolicyversion" actionName)))))

; Action: p1.22
(declare-const p1.22.action Bool)
(assert (= p1.22.action (or (and (= "mediastore" actionNamespace) (= "deletecontainerpolicy" actionName)) (and (= "mediastore" actionNamespace) (= "putcontainerpolicy" actionName)))))

; Action: p1.23
(declare-const p1.23.action Bool)
(assert (= p1.23.action (or (and (= "opsworks" actionNamespace) (= "setpermission" actionName)) (and (= "opsworks" actionNamespace) (= "updateuserprofile" actionName)))))

; Action: p1.24
(declare-const p1.24.action Bool)
(assert (= p1.24.action (or (and (= "redshift" actionNamespace) (= "authorizeclustersecuritygroupin_ress" actionName)) (and (= "redshift" actionNamespace) (= "authorizesnapshotaccess" actionName)) (and (= "redshift" actionNamespace) (= "createclusteruser" actionName)) (and (= "redshift" actionNamespace) (= "createsnapshotcopygrant" actionName)) (and (= "redshift" actionNamespace) (= "joingroup" actionName)) (and (= "redshift" actionNamespace) (= "modifyclusteriamroles" actionName)) (and (= "redshift" actionNamespace) (= "revokeclustersecuritygroupin_ress" actionName)) (and (= "redshift" actionNamespace) (= "revokesnapshotaccess" actionName)) (and (= "redshift" actionNamespace) (= "rotateencryptionkey" actionName)))))

; Policy: 1
(declare-const p1.denies Bool)
(assert (= p1.denies (or p1.1.action p1.2.action p1.3.action p1.4.action p1.5.action p1.6.action p1.7.action p1.8.action p1.9.action p1.10.action p1.11.action p1.12.action p1.13.action p1.14.action p1.15.action p1.16.action p1.17.action p1.18.action p1.19.action p1.20.action p1.21.action p1.22.action p1.23.action p1.24.action)))
(declare-const p1.allows Bool)
(assert (= p1.allows (not p1.denies)))
(declare-const p1.neutral Bool)
(assert (= p1.neutral (and p1.denies (not p1.denies))))

; The valid resources for sts actions are sts, iam
(assert (=> (= actionNamespace "sts") (or (= resource_service "sts") (= resource_service "iam"))))

; The valid resources for iam actions are sts, iam
(assert (=> (= actionNamespace "iam") (or (= resource_service "sts") (= resource_service "iam"))))

; The only valid action namespaces for sns resources is sns and vice versa
(assert (= (= resource_service "sns") (= actionNamespace "sns")))

; The only valid action namespaces for s3 resources is s3 and vice versa
(assert (= (= resource_service "s3") (= actionNamespace "s3")))

; The only valid action namespaces for lambda resources is lambda and vice versa
(assert (= (= resource_service "lambda") (= actionNamespace "lambda")))

; The valid action namespaces for sts resources are iam, sts
(assert (=> (= resource_service "sts") (or (= actionNamespace "iam") (= actionNamespace "sts"))))

; The only valid action namespaces for sqs resources is sqs and vice versa
(assert (= (= resource_service "sqs") (= actionNamespace "sqs")))

; The valid action namespaces for iam resources are iam, sts
(assert (=> (= resource_service "iam") (or (= actionNamespace "iam") (= actionNamespace "sts"))))

; The only valid action namespaces for glacier resources is glacier and vice versa
(assert (= (= resource_service "glacier") (= actionNamespace "glacier")))

; The only valid action namespaces for kms resources is kms and vice versa
(assert (= (= resource_service "kms") (= actionNamespace "kms")))

; The only valid action namespaces for es resources is es and vice versa
(assert (= (= resource_service "es") (= actionNamespace "es")))

; resource prefix invariant
(assert (= "arn" resource_prefix))

; resource partition and region invariant
(assert (or (and (= "aws" resource_partition) (= "ap-east-1" resource_region)) (and (= "aws" resource_partition) (= "" resource_region)) (and (= "aws" resource_partition) (= "ap-northeast-1" resource_region)) (and (= "aws" resource_partition) (= "ap-northeast-2" resource_region)) (and (= "aws" resource_partition) (= "ap-northeast-3" resource_region)) (and (= "aws" resource_partition) (= "ap-south-1" resource_region)) (and (= "aws" resource_partition) (= "ap-southeast-1" resource_region)) (and (= "aws" resource_partition) (= "ap-southeast-2" resource_region)) (and (= "aws" resource_partition) (= "ca-central-1" resource_region)) (and (= "aws" resource_partition) (= "eu-central-1" resource_region)) (and (= "aws" resource_partition) (= "eu-north-1" resource_region)) (and (= "aws" resource_partition) (= "eu-west-1" resource_region)) (and (= "aws" resource_partition) (= "eu-west-2" resource_region)) (and (= "aws" resource_partition) (= "eu-west-3" resource_region)) (and (= "aws" resource_partition) (= "me-south-1" resource_region)) (and (= "aws" resource_partition) (= "sa-east-1" resource_region)) (and (= "aws" resource_partition) (= "us-east-1" resource_region)) (and (= "aws" resource_partition) (= "us-east-2" resource_region)) (and (= "aws" resource_partition) (= "us-west-1" resource_region)) (and (= "aws" resource_partition) (= "us-west-2" resource_region))))

; resource service invariant
(assert (str.in_re resource_service (re.* (re.union (re.range "a" "z") (re.range "0" "9") (str.to_re "-")))))

; resource account invariant
(assert (str.in_re resource_account (re.union (str.to_re "") ((_ re.loop 12 12) (re.range "0" "9")))))

; Goals
(assert p0.allows)
(assert (not p1.allows))
(check-sat)
