package main

import (
	"encoding/base64"
	"flag"
	"fmt"
	"log"
	"math/big"
	"net/http"
	"regexp"
	"time"
	_"database/sql"

	ct "github.com/google/certificate-transparency-go"
	"github.com/google/certificate-transparency-go/client"
	"github.com/google/certificate-transparency-go/jsonclient"
	"github.com/google/certificate-transparency-go/scanner"
	"github.com/lib/pq"
	"database/sql"
	_"os"
	_"runtime/trace"
	"sync"
	_"unicode/utf8"
	_"strconv"
	_"strings"
	_"crypto/md5"
	_"encoding/hex"
	"encoding/hex"
	"crypto/x509"
	"strings"
	"strconv"
	"golang.org/x/net/context"
	_"encoding/pem"
	_"encoding/pem"
	_"bytes"
	"crypto/sha256"
	"os"
	_"runtime/trace"
	"io"
	"encoding/csv"
	"bufio"
)


const (
	// matchesNothingRegex is a regex which cannot match any input.
	matchesNothingRegex = "a^"
)

var logURI = flag.String("log_uri", "https://ct.googleapis.com/daedalus", "CT log base URI") //1000000
var matchSubjectRegex = flag.String("match_subject_regex", ".*", "Regex to match CN/SAN")
var matchIssuerRegex = flag.String("match_issuer_regex", "", "Regex to match in issuer CN")
var precertsOnly = flag.Bool("precerts_only", false, "Only match precerts")
var serialNumber = flag.String("serial_number", "", "Serial number of certificate of interest")
var batchSize = flag.Int("batch_size", 1000, "Max number of entries to request at per call to get-entries")
var numWorkers = flag.Int("num_workers", 1000, "Number of concurrent matchers")
var parallelFetch = flag.Int("parallel_fetch", 8, "Number of concurrent GetEntries fetches")
var startIndex = flag.Int64("start_index", 0, "Log index to start scanning at")
var quiet = flag.Bool("quiet", false, "Don't print out extra logging messages, only matches.")
var printChains = flag.Bool("print_chains", false, "If true prints the whole chain rather than a summary")


var logs = make(map[string]string)

var channel = make(chan (*ct.LogEntry))


// Structs to pass through channels

type stmt_and_chain_cert struct {
	stmt *sql.Stmt
	cert *x509.Certificate
}

type stmt_and_entry struct {
	stmt_entry *sql.Stmt
	stmt_cert *sql.Stmt
	stmt_chain *sql.Stmt
	entry *ct.LogEntry
}

type stmt_and_precert_entry struct {
	stmt_entry *sql.Stmt
	stmt_cert *sql.Stmt
	stmt_chain *sql.Stmt
	precert_entry *ct.LogEntry
}

type alter_table struct{
	stmt *sql.Stmt
	inclusion_time uint64
	max_path_len int
	cert_hash string
}

// Mutex for hash map access
var mutex = &sync.Mutex{}


// Parse certificate entry and execute DB statements for entry and cert table
func parse_and_exec_cert(c chan(*ct.LogEntry), wg *sync.WaitGroup, channel_chain chan(*x509.Certificate)) {
	var log_id = logs[*logURI]
	// Execute DB statements
	db, err := sql.Open("postgres", "user=postgres password=postgres dbname=ct2 sslmode=disable")
	if err != nil {
		log.Fatal(err)
	}
	defer db.Close()
	for e := range c {
		// Get values for all DB columns

		inclusion_time := e.Leaf.TimestampedEntry.Timestamp;
		max_path_len := e.X509Cert.MaxPathLen;
		var ip_tmp []string
		for _, ip := range e.X509Cert.IPAddresses {
			// strings.Trim and QuoteToASCII is used to handle characters postgres doesnt accept,
			// like chinese double byte chars. Get encoded as \x<byte value>
			ip_tmp = append(ip_tmp, strings.Trim(strconv.QuoteToASCII(ip.String()), "\""))
		}
		san_ip := pq.Array(ip_tmp)
		is_ca := e.X509Cert.IsCA
		common_name := strings.Trim(strconv.QuoteToASCII(e.X509Cert.Subject.CommonName), "\"")
		var dns_names_tmp []string
		for _, name := range e.X509Cert.DNSNames {
			dns_names_tmp = append(dns_names_tmp, strings.Trim(strconv.QuoteToASCII(name), "\""))
		}
		san_dns := pq.Array(dns_names_tmp)
		index := e.Index
		cert_hash_tmp := sha256.Sum256(e.X509Cert.Raw)
		cert_hash := hex.EncodeToString(cert_hash_tmp[:])
		cert := &e.X509Cert.Raw
		pub_key := &e.X509Cert.RawSubjectPublicKeyInfo
		var a7_tmp []string
		for _, chain_entry := range e.Chain {
			chain_cert, err := x509.ParseCertificate(chain_entry.Data)
			if err != nil {
				continue
			}
			//var pass_to_channel stmt_and_chain_cert
			//pass_to_channel.cert = chain_cert
			//pass_to_channel.stmt = e.stmt_chain
			channel_chain <- chain_cert
			tmp_sha256 := sha256.Sum256(chain_entry.Data)
			a7_tmp = append(a7_tmp, hex.EncodeToString(tmp_sha256[:]))
		}
		chain_entries := pq.Array(a7_tmp)
		issuer_cn := strings.Trim(strconv.QuoteToASCII(e.X509Cert.Issuer.CommonName), "\"")
		signature_algorithm := &e.X509Cert.SignatureAlgorithm
		pub_key_algorithm := &e.X509Cert.PublicKeyAlgorithm
		not_before := e.X509Cert.NotBefore
		not_after := e.X509Cert.NotAfter
		var a12_tmp []string
		for _, identifier := range e.X509Cert.PolicyIdentifiers {
			a12_tmp = append(a12_tmp, identifier.String())
		}
		policy_identifiers := pq.Array(a12_tmp)
		x509_version := e.X509Cert.Version
		key_usage := strings.Trim(strconv.QuoteToASCII(string(x509.KeyUsage(e.X509Cert.KeyUsage))), "\"")
		var a14_tmp []string
		for _, ext := range e.X509Cert.ExtKeyUsage {
			a14_tmp = append(a14_tmp, strings.Trim(strconv.QuoteToASCII(string(x509.ExtKeyUsage(ext))), "\""))
		}
		ext_key_usage := pq.Array(a14_tmp)
		basic_constraints := &e.X509Cert.BasicConstraintsValid
		var a16_tmp []string
		for _, policy := range e.X509Cert.PolicyIdentifiers {
			a16_tmp = append(a16_tmp, policy.String())
		}
		cert_policies := pq.Array(a16_tmp)
		var a18_tmp []string
		for _, extension := range e.X509Cert.Extensions {
			a18_tmp = append(a18_tmp, extension.Id.String())
		}
		extensions := pq.Array(a18_tmp)
		var a19_tmp []string
		for _, unhandled := range e.X509Cert.UnhandledCriticalExtensions {
			a19_tmp = append(a19_tmp, unhandled.String())
		}
		unhandled_extensions := pq.Array(a19_tmp)
		var san_email_tmp []string
		for _, email := range e.X509Cert.EmailAddresses {
			san_email_tmp = append(san_email_tmp, strings.Trim(strconv.QuoteToASCII(email), "\""))
		}
		san_email := pq.Array(san_email_tmp)


		_, err = db.Exec("INSERT INTO entry VALUES($1, $2, $3, $4, $5);", log_id, logURI, index, cert_hash, chain_entries)
		//_, err := e.stmt_entry.Exec(log_id, logURI, index, cert_hash, chain_entries)
		if err != nil {
			log.Fatal(err)
		}
		_, err = db.Exec("INSERT INTO cert VALUES($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12, $13, $14, $15, $16, $17, $18, $19, $20, $21, $22, $23) ON CONFLICT (cert_hash) DO NOTHING;", cert_hash, cert, is_ca, common_name, san_dns, san_ip, san_email, issuer_cn, pub_key, signature_algorithm, pub_key_algorithm, not_before, not_after, policy_identifiers, x509_version, key_usage, ext_key_usage, basic_constraints, cert_policies, extensions, unhandled_extensions, inclusion_time, max_path_len)
		//_, err = e.stmt_cert.Exec(cert_hash, cert, is_ca, common_name, san_dns, san_ip, san_email, issuer_cn, pub_key, signature_algorithm, pub_key_algorithm, not_before, not_after, policy_identifiers, x509_version, key_usage, ext_key_usage, basic_constraints, cert_policies, extensions, unhandled_extensions, inclusion_time, max_path_len)
		if err != nil {
			log.Fatal(err)
		}

	}
	wg.Done()
}


// Parse Precert entry and execute DB statements for entry and cert table
func parse_and_exec_precert(c chan(*ct.LogEntry), wg *sync.WaitGroup, channel_chain chan(*x509.Certificate)) {
	var log_id = logs[*logURI]
	// Execute DB statements
	db, err := sql.Open("postgres", "user=postgres password=postgres dbname=ct2 sslmode=disable")
	if err != nil {
		log.Fatal(err)
	}
	defer db.Close()
	for e := range c {
		inclusion_time := e.Leaf.TimestampedEntry.Timestamp;
		max_path_len := e.Precert.TBSCertificate.MaxPathLen;
		var ip_tmp []string
		for _, ip := range e.Precert.TBSCertificate.IPAddresses {
			ip_tmp = append(ip_tmp, strings.Trim(strconv.QuoteToASCII(ip.String()), "\""))
		}
		san_ip := pq.Array(ip_tmp)
		is_ca := e.Precert.TBSCertificate.IsCA
		common_name := strings.Trim(strconv.QuoteToASCII(e.Precert.TBSCertificate.Subject.CommonName), "\"")
		var dns_names_tmp []string
		for _, name := range e.Precert.TBSCertificate.DNSNames {
			dns_names_tmp = append(dns_names_tmp, strings.Trim(strconv.QuoteToASCII(name), "\""))
		}
		san_dns := pq.Array(dns_names_tmp)
		index := e.Index
		cert_hash_tmp := sha256.Sum256(e.Precert.TBSCertificate.Raw)
		cert_hash := hex.EncodeToString(cert_hash_tmp[:])
		cert := &e.Precert.TBSCertificate.Raw
		pub_key := &e.Precert.TBSCertificate.RawSubjectPublicKeyInfo
		var a7_tmp []string
		for _, chain_entry := range e.Chain {
			chain_cert, err := x509.ParseCertificate(chain_entry.Data)
			if err != nil {
				continue
			}
			//var pass_to_channel stmt_and_chain_cert
			//pass_to_channel.cert = chain_cert
			//pass_to_channel.stmt = e.stmt_chain
			channel_chain <- chain_cert
			tmp_sha256 := sha256.Sum256(chain_entry.Data)
			a7_tmp = append(a7_tmp, hex.EncodeToString(tmp_sha256[:]))
		}
		chain_entries := pq.Array(a7_tmp)
		issuer_cn := strings.Trim(strconv.QuoteToASCII(e.Precert.TBSCertificate.Issuer.CommonName), "\"")
		signature_algorithm := &e.Precert.TBSCertificate.SignatureAlgorithm
		pub_key_algorithm := &e.Precert.TBSCertificate.PublicKeyAlgorithm
		not_before := e.Precert.TBSCertificate.NotBefore
		not_after := e.Precert.TBSCertificate.NotAfter
		var a12_tmp []string
		for _, identifier := range e.Precert.TBSCertificate.PolicyIdentifiers {
			a12_tmp = append(a12_tmp, identifier.String())
		}
		policy_identifiers := pq.Array(a12_tmp)
		x509_version := e.Precert.TBSCertificate.Version
		key_usage := strings.Trim(strconv.QuoteToASCII(string(x509.KeyUsage(e.Precert.TBSCertificate.KeyUsage))), "\"")
		var a14_tmp []string
		for _, ext := range e.Precert.TBSCertificate.ExtKeyUsage {
			a14_tmp = append(a14_tmp, strings.Trim(strconv.QuoteToASCII(string(x509.ExtKeyUsage(ext))), "\""))
		}
		ext_key_usage := pq.Array(a14_tmp)
		basic_constraints := &e.Precert.TBSCertificate.BasicConstraintsValid
		var a16_tmp []string
		for _, policy := range e.Precert.TBSCertificate.PolicyIdentifiers {
			a16_tmp = append(a16_tmp, policy.String())
		}
		cert_policies := pq.Array(a16_tmp)
		var a18_tmp []string
		for _, extension := range e.Precert.TBSCertificate.Extensions {
			a18_tmp = append(a18_tmp, extension.Id.String())
		}
		extensions := pq.Array(a18_tmp)
		var a19_tmp []string
		for _, unhandled := range e.Precert.TBSCertificate.UnhandledCriticalExtensions {
			a19_tmp = append(a19_tmp, unhandled.String())
		}
		unhandled_extensions := pq.Array(a19_tmp)
		var san_email_tmp []string
		for _, email := range e.Precert.TBSCertificate.EmailAddresses {
			san_email_tmp = append(san_email_tmp, strings.Trim(strconv.QuoteToASCII(email), "\""))
		}
		san_email := pq.Array(san_email_tmp)


		_, err = db.Exec("INSERT INTO entry VALUES($1, $2, $3, $4, $5);", log_id, logURI, index, cert_hash, chain_entries)
		//_, err := e.stmt_entry.Exec(log_id, logURI, index, cert_hash, chain_entries)
		if err != nil {
			log.Fatal(err)
		}
		_, err = db.Exec("INSERT INTO cert VALUES($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12, $13, $14, $15, $16, $17, $18, $19, $20, $21, $22, $23) ON CONFLICT (cert_hash) DO NOTHING;", cert_hash, cert, is_ca, common_name, san_dns, san_ip, san_email, issuer_cn, pub_key, signature_algorithm, pub_key_algorithm, not_before, not_after, policy_identifiers, x509_version, key_usage, ext_key_usage, basic_constraints, cert_policies, extensions, unhandled_extensions, inclusion_time, max_path_len)
		//_, err = e.stmt_cert.Exec(cert_hash, cert, is_ca, common_name, san_dns, san_ip, san_email, issuer_cn, pub_key, signature_algorithm, pub_key_algorithm, not_before, not_after, policy_identifiers, x509_version, key_usage, ext_key_usage, basic_constraints, cert_policies, extensions, unhandled_extensions, inclusion_time, max_path_len)
		if err != nil {
			log.Fatal(err)
		}

	}
	wg.Done()
}


// If chain cert not in hash map: Parse chain cert and execute DB statemnts for chain_cert table
func parse_and_exec_chain_cert(c chan(*x509.Certificate), wg *sync.WaitGroup, chain_hashes *map[string](int)) {
	// Execute DB statements
	db, err := sql.Open("postgres", "user=postgres password=postgres dbname=ct2 sslmode=disable")
	if err != nil {
		log.Fatal(err)
	}
	defer db.Close()
	for e := range c {
		cert_hash_tmp := sha256.Sum256(e.Raw)
		cert_hash := hex.EncodeToString(cert_hash_tmp[:])
		//mutex.Lock()
		//_, ok := (*chain_hashes)[cert_hash]
		//mutex.Unlock()
		//if ok {

		//fmt.Println("cert_hash already exists!")
		//} else {
		var ip_tmp []string
		for _, ip := range e.IPAddresses {
			ip_tmp = append(ip_tmp, strings.Trim(strconv.QuoteToASCII(ip.String()), "\""))
		}
		san_ip := pq.Array(ip_tmp)
		is_ca := e.IsCA
		common_name := strings.Trim(strconv.QuoteToASCII(e.Subject.CommonName), "\"")
		var dns_names_tmp []string
		for _, name := range e.DNSNames {
			dns_names_tmp = append(dns_names_tmp, strings.Trim(strconv.QuoteToASCII(name), "\""))
		}
		san_dns := pq.Array(dns_names_tmp)
		cert := &e.Raw
		pub_key := &e.RawSubjectPublicKeyInfo
		issuer_cn := strings.Trim(strconv.QuoteToASCII(e.Issuer.CommonName), "\"")
		signature_algorithm := &e.SignatureAlgorithm
		pub_key_algorithm := &e.PublicKeyAlgorithm
		not_before := e.NotBefore
		not_after := e.NotAfter
		var a12_tmp []string
		for _, identifier := range e.PolicyIdentifiers {
			a12_tmp = append(a12_tmp, identifier.String())
		}
		policy_identifiers := pq.Array(a12_tmp)
		x509_version := e.Version
		key_usage := strings.Trim(strconv.QuoteToASCII(string(x509.KeyUsage(e.KeyUsage))), "\"")
		var a14_tmp []string
		for _, ext := range e.ExtKeyUsage {
			a14_tmp = append(a14_tmp, strings.Trim(strconv.QuoteToASCII(string(x509.ExtKeyUsage(ext))), "\""))
		}
		ext_key_usage := pq.Array(a14_tmp)
		basic_constraints := &e.BasicConstraintsValid
		var a16_tmp []string
		for _, policy := range e.PolicyIdentifiers {
			a16_tmp = append(a16_tmp, policy.String())
		}
		cert_policies := pq.Array(a16_tmp)
		var a18_tmp []string
		for _, extension := range e.Extensions {
			a18_tmp = append(a18_tmp, extension.Id.String())
		}
		extensions := pq.Array(a18_tmp)
		var a19_tmp []string
		for _, unhandled := range e.UnhandledCriticalExtensions {
			a19_tmp = append(a19_tmp, unhandled.String())
		}
		unhandled_extensions := pq.Array(a19_tmp)
		var san_email_tmp []string
		for _, email := range e.EmailAddresses {
			san_email_tmp = append(san_email_tmp, strings.Trim(strconv.QuoteToASCII(email), "\""))
		}
		san_email := pq.Array(san_email_tmp)

		_,err = db.Exec("INSERT INTO chain_cert VALUES($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12, $13, $14, $15, $16, $17, $18, $19, $20, $21) ON CONFLICT (cert_hash) DO NOTHING;", cert_hash, cert, is_ca, common_name, san_dns, san_ip, san_email, issuer_cn, pub_key, signature_algorithm, pub_key_algorithm, not_before, not_after, policy_identifiers, x509_version, key_usage, ext_key_usage, basic_constraints, cert_policies, extensions, unhandled_extensions)
		//_, err2 := e.stmt.Exec(cert_hash, cert, is_ca, common_name, san_dns, san_ip, san_email, issuer_cn, pub_key, signature_algorithm, pub_key_algorithm, not_before, not_after, policy_identifiers, x509_version, key_usage, ext_key_usage, basic_constraints, cert_policies, extensions, unhandled_extensions)
		if err != nil {
			log.Fatal(err)
		}
		//err := e.stmt.Close()
		//if err != nil {
		//	log.Fatal(err)
		//}
		//mutex.Lock()
		//(*chain_hashes)[cert_hash] = 0
		//mutex.Unlock()
		//	}
	}
	wg.Done()
}

func func_alter_table(c chan(*alter_table), wg *sync.WaitGroup) {
	for e := range c {
		_, err := e.stmt.Exec(e.inclusion_time, e.max_path_len, e.cert_hash)
		if err != nil {
			log.Fatal(err)
		}
	}
	wg.Done()
}


// Prepare statements of DB transactions and decide wheter cert or precert
// When log is completed, execute DB transactions and close channels
func switchEntryType(c chan(*ct.LogEntry), wg *sync.WaitGroup, table_name string, NumWorkers int, chain_hashes *map[string](int), channel_entry chan(*ct.LogEntry), channel_precert chan(*ct.LogEntry)) {
	// Loop over all log entries

	for e := range c {
		switch e.Leaf.TimestampedEntry.EntryType {
		case ct.X509LogEntryType:
			//var pass_to_channel stmt_and_entry
			//pass_to_channel.entry = e
			//pass_to_channel.stmt_entry = stmt
			//pass_to_channel.stmt_cert = stmt2
			//pass_to_channel.stmt_chain = stmt3
			channel_entry <- e

		case ct.PrecertLogEntryType:
			//var pass_to_channel stmt_and_precert_entry
			//pass_to_channel.precert_entry = e
			//pass_to_channel.stmt_entry = stmt
			//pass_to_channel.stmt_cert = stmt2
			//pass_to_channel.stmt_chain = stmt3
			channel_precert <- e
		}
	}


	// Log is done! Close everything and commit transactions

	wg.Done()

}


func logCertInfo(entry *ct.LogEntry) {
	channel <- entry
}

// Prints out a short bit of info about |precert|, found at |index| in the
// specified log
func logPrecertInfo(entry *ct.LogEntry) {
	channel <- entry
}

func chainToString(certs []ct.ASN1Cert) string {
	var output []byte

	for _, cert := range certs {
		output = append(output, cert.Data...)
	}

	return base64.StdEncoding.EncodeToString(output)
}

func logFullChain(entry *ct.LogEntry) {
	log.Printf("Index %d: Chain: %s", entry.Index, chainToString(entry.Chain))
}

func createRegexes(regexValue string) (*regexp.Regexp, *regexp.Regexp) {
	// Make a regex matcher
	var certRegex *regexp.Regexp
	precertRegex := regexp.MustCompile(regexValue)
	switch *precertsOnly {
	case true:
		certRegex = regexp.MustCompile(matchesNothingRegex)
	case false:
		certRegex = precertRegex
	}

	return certRegex, precertRegex
}

func createMatcherFromFlags() (scanner.Matcher, error) {
	if *matchIssuerRegex != "" {
		certRegex, precertRegex := createRegexes(*matchIssuerRegex)
		return scanner.MatchIssuerRegex{
			CertificateIssuerRegex:    certRegex,
			PrecertificateIssuerRegex: precertRegex}, nil
	}
	if *serialNumber != "" {
		log.Printf("Using SerialNumber matcher on %s", *serialNumber)
		var sn big.Int
		_, success := sn.SetString(*serialNumber, 0)
		if !success {
			return nil, fmt.Errorf("Invalid serialNumber %s", *serialNumber)
		}
		return scanner.MatchSerialNumber{SerialNumber: sn}, nil
	}
	certRegex, precertRegex := createRegexes(*matchSubjectRegex)
	return scanner.MatchSubjectRegex{
		CertificateSubjectRegex:    certRegex,
		PrecertificateSubjectRegex: precertRegex}, nil
}


// Get last tree_size of specified log from DB and return it
func set_starting_index_from_db() int64 {
	var log_id = logs[*logURI]
	last_sth := 0
	db, err := sql.Open("postgres", "user=postgres password=postgres dbname=ct2 sslmode=disable")
	if err != nil {
		log.Fatal(err)
	}
	rows, err := db.Query("SELECT tree_size FROM ct_log WHERE log_id=$1", log_id)
	if err != nil {
		log.Fatal(err)
	}
	for rows.Next() {
		err := rows.Scan(&last_sth)
		if err != nil {
			log.Fatal(err)
		}
		fmt.Println("Last STH from DB: %d", last_sth)
	}
	rows.Close()
	return int64(last_sth)
	//return int64(0)
}

// Write new tree_size of downloaded log to DB
func update_sth(sth uint64) {
	var log_id = logs[*logURI]
	db, err := sql.Open("postgres", "user=postgres password=postgres dbname=ct2 sslmode=disable")
	if err != nil {
		log.Fatal(err)
	}
	defer db.Close()
	rows, err := db.Query("UPDATE ct_log SET tree_size=$2, last_download=$3  WHERE log_id=$1;", log_id, sth, time.Now().UTC())
	if err != nil {
		log.Fatal(err)
	}
	rows.Close()
	rows2, err := db.Query("INSERT INTO ct_log (log_id, log_url, tree_size, last_download) SELECT $1, $2, $3, $4 WHERE NOT EXISTS (SELECT 1 FROM ct_log WHERE log_id=$1);", logs[*logURI], logURI, sth, time.Now().UTC())
	if err != nil {
		log.Fatal(err)
	}
	rows2.Close()
}

// Create DB tables if not exist
func create_new_table(name string) {
	db, err := sql.Open("postgres", "user=postgres password=postgres dbname=ct2 sslmode=disable")
	if err != nil {
		log.Fatal(err)
	}
	defer db.Close()
	rows, err := db.Query("CREATE TABLE if not exists " + name + " ( cert_hash text PRIMARY KEY, cert bytea, is_ca boolean, common_name text, san_dns text[], san_ip text[], san_email text[], issuer_cn text, pub_key bytea, signature_algorithm text, pub_key_algorithm text, not_before timestamp with time zone, not_after timestamp with time zone, policy_identifiers text[], x509_version integer, key_usage text, ext_key_usage text[], basic_constraints text, cert_policies text[], extensions text[], unhandled_extensions text[] );")
	if err != nil {
		log.Fatal(err)
	}
	defer rows.Close()
	rows2, err := db.Query("CREATE TABLE if not exists " + "chain_" + name + " ( cert_hash text PRIMARY KEY, cert bytea, is_ca boolean, common_name text, san_dns text[], san_ip text[], san_email text[], issuer_cn text, pub_key bytea, signature_algorithm text, pub_key_algorithm text, not_before timestamp with time zone, not_after timestamp with time zone, policy_identifiers text[], x509_version integer, key_usage text, ext_key_usage text[], basic_constraints text, cert_policies text[], extensions text[], unhandled_extensions text[] );")
	if err != nil {
		log.Fatal(err)
	}
	defer rows2.Close()
}

// Create map of hash values from chain_cert table
func select_chain_hashes_from_db() map[string](int) {
	db, err := sql.Open("postgres", "user=postgres password=postgres dbname=ct2 sslmode=disable")
	if err != nil {
		log.Fatal(err)
	}
	defer db.Close()

	rows, err := db.Query("SELECT cert_hash from chain_cert WHERE is_ca=true and issuer_cn != 'Merge Delay Intermediate 1' and common_name!='';")
	if err != nil {
		log.Fatal(err)
	}
	m := make(map[string]int)
	var res []string
	for rows.Next() {
		tmp := ""
		err := rows.Scan(&tmp)
		if err != nil {
			log.Fatal(err)
		}
		res = append(res, tmp)
	}
	for _, r := range res {
		m[r] = 0
	}
	return m
}

func initializeLogMap(){
	fh, err := os.Open("logs.latest.csv")
	if err != nil {
		log.Fatal(err)
	}
	defer fh.Close()
	r := csv.NewReader(bufio.NewReader(fh))
	for {
		record, err := r.Read()

		// Stop at EOF
		if err == io.EOF {
			break
		}
		logs[record[1]] = record[0]
	}
}

func main() {

	// Initialize map of logs
	initializeLogMap()

	log.SetFlags(log.Lshortfile)
	flag.Parse()
	logClient, err := client.New(*logURI, &http.Client{
		Timeout: 10 * time.Second,
		Transport: &http.Transport{
			TLSHandshakeTimeout:   30 * time.Second,
			ResponseHeaderTimeout: 30 * time.Second,
			MaxIdleConnsPerHost:   10,
			DisableKeepAlives:     false,
			//MaxIdleConns:          100,
			//IdleConnTimeout:       90 * time.Second,
			ExpectContinueTimeout: 1 * time.Second,
		},
	}, jsonclient.Options{})
	if err != nil {
		log.Fatal(err)
	}
	matcher, err := createMatcherFromFlags()
	if err != nil {
		log.Fatal(err)
	}

	opts := scanner.ScannerOptions{
		Matcher:       matcher,
		BatchSize:     *batchSize,
		NumWorkers:    *numWorkers,
		ParallelFetch: *parallelFetch,
		StartIndex:    set_starting_index_from_db(),
		Quiet:         *quiet,
	}
	scanner := scanner.NewScanner(logClient, opts)

	//latestSth, err := logClient.GetSTH(context.Background())
	//if err != nil {
	//		log.Fatal(err)
	//	}

	// Use when creating temp tables and CopyIn
	table_name := strings.Replace(*logURI, "/", "", -1)
	table_name = strings.Replace(table_name, ":", "", -1)
	table_name = strings.Replace(table_name, ".", "", -1)
	table_name = strings.Replace(table_name, "-", "", -1)
	table_name = "cert_" + table_name
	//create_new_table(table_name)

	// Use when using UPSERT
	//create_new_table("cert")

	// Hash map of chain certs
	//chain_hashes := select_chain_hashes_from_db()
	var chain_hashes map[string](int)


	// Channels and their waitgroups
	//
	var channel_chain = make(chan (*x509.Certificate))
	var channel_entry = make(chan (*ct.LogEntry))
	var channel_precert = make(chan (*ct.LogEntry))

	var wg_entry sync.WaitGroup
	wg_entry.Add(opts.NumWorkers)
	for w := 0; w < opts.NumWorkers; w++ {

		go parse_and_exec_cert(channel_entry, &wg_entry, channel_chain)
	}


	var wg_precert sync.WaitGroup
	wg_precert.Add(opts.NumWorkers)
	for w := 0; w < opts.NumWorkers; w++ {

		go parse_and_exec_precert(channel_precert, &wg_precert, channel_chain)
	}


	var wg_chain sync.WaitGroup
	wg_chain.Add(opts.NumWorkers)
	for w := 0; w < opts.NumWorkers; w++ {

		go parse_and_exec_chain_cert(channel_chain, &wg_chain, &chain_hashes)
	}


	var wg sync.WaitGroup
	wg.Add(opts.NumWorkers)
	for w := 0; w < opts.NumWorkers; w++ {

		go switchEntryType(channel, &wg, table_name, opts.NumWorkers, &chain_hashes, channel_entry, channel_precert)
	}

	ctx := context.Background()
	var latestSth int64
	if *printChains {
		latestSth, err = scanner.Scan(ctx, logFullChain, logFullChain)
	} else {
		latestSth, err = scanner.Scan(ctx, logCertInfo, logPrecertInfo)
	}
	// DONE close everything! Care: Look for deadlocks of channels.

	close(channel)
	wg.Wait()

	close(channel_entry)
	wg_entry.Wait()

	close(channel_precert)
	wg_precert.Wait()


	close(channel_chain)
	wg_chain.Wait()

	// Write new tree_size to ct_log table
	fmt.Printf("Writing STH of %d to DB\n", latestSth)
	update_sth(uint64(latestSth))
}