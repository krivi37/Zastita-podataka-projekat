package implementation;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.math.BigInteger;

import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.KeyStore;
import java.security.KeyStore.PasswordProtection;
import java.security.KeyStore.PrivateKeyEntry;
import java.security.KeyStoreException;
import java.security.PrivateKey;
import java.security.Provider;
import java.security.PublicKey;
import java.security.SecureRandom;
import java.security.Security;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Date;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Vector;

import javax.security.auth.x500.X500Principal;

import java.security.cert.CertificateFactory;
import java.security.cert.X509Certificate;
import java.security.interfaces.DSAPublicKey;
import java.security.interfaces.RSAPublicKey;
import java.security.spec.ECGenParameterSpec; //ovo sam koristio kod provjere za EC kljuceve, posto aplikacija moze da uveze i EC kljuceve
import java.security.interfaces.ECPublicKey;


import org.bouncycastle.asn1.x500.X500NameStyle;
import org.bouncycastle.asn1.x500.AttributeTypeAndValue;
import org.bouncycastle.asn1.x500.RDN;
import org.bouncycastle.asn1.x500.X500Name;
import org.bouncycastle.asn1.x500.style.IETFUtils;
import org.bouncycastle.asn1.x500.style.RFC4519Style;
import org.bouncycastle.asn1.ASN1ObjectIdentifier;
import org.bouncycastle.asn1.ASN1Sequence;
import org.bouncycastle.asn1.cms.ContentInfo;
import org.bouncycastle.asn1.x509.AlgorithmIdentifier;
import org.bouncycastle.asn1.x509.BasicConstraints;
import org.bouncycastle.asn1.x509.Extension;
import org.bouncycastle.asn1.x509.GeneralName;
import org.bouncycastle.asn1.x509.GeneralNames;
import org.bouncycastle.asn1.x509.KeyUsage;
import org.bouncycastle.cert.X509v3CertificateBuilder;
import org.bouncycastle.cert.jcajce.JcaCertStore;
import org.bouncycastle.cert.jcajce.JcaX509CertificateConverter;
import org.bouncycastle.cert.jcajce.JcaX509CertificateHolder;
import org.bouncycastle.cms.CMSProcessableByteArray;
import org.bouncycastle.cms.CMSSignedData;
import org.bouncycastle.cms.CMSSignedDataGenerator;
import org.bouncycastle.cms.CMSTypedData;
import org.bouncycastle.cms.jcajce.JcaSignerInfoGeneratorBuilder;
import org.bouncycastle.jce.provider.BouncyCastleProvider;
import org.bouncycastle.openssl.PEMParser;
import org.bouncycastle.openssl.jcajce.JcaPEMWriter;
import org.bouncycastle.operator.ContentSigner;
import org.bouncycastle.operator.DefaultAlgorithmNameFinder;
import org.bouncycastle.operator.jcajce.JcaContentSignerBuilder;
import org.bouncycastle.operator.jcajce.JcaDigestCalculatorProviderBuilder;
import org.bouncycastle.pkcs.PKCS10CertificationRequest;
import org.bouncycastle.pkcs.PKCS10CertificationRequestBuilder;
import org.bouncycastle.pkcs.jcajce.JcaPKCS10CertificationRequestBuilder;
import org.bouncycastle.util.Store;
import org.bouncycastle.asn1.x509.SubjectPublicKeyInfo;


import code.GuiException;
import gui.Constants;
import gui.GuiInterfaceV1;
import x509.v3.CodeV3;
import x509.v3.GuiV3;

public class MyCode extends CodeV3 {
	private KeyStore key_store;
	private PasswordProtection password;
	private String set=null;
	protected GuiV3 access;
	private SubjectPublicKeyInfo javniCSR=null;
	
	@Override
	public Enumeration<String> loadLocalKeystore() {
		try {
			key_store = KeyStore.getInstance("PKCS12");
			key_store.load(null);
			return key_store.aliases();
			
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}
	
	@Override
	public void resetLocalKeystore() {
		try {
			Enumeration<String>aliases = key_store.aliases();
			Vector<String>vector=new Vector<String>();
			while(aliases.hasMoreElements()) {
				vector.add(aliases.nextElement());
				}
			
			for (String s:vector) {//radjeno ovako zato sto enumeration baca concurrent modification exception posto se modifikuju aliasi keystore-a
				this.removeKeypair(s);
			}
			
		} catch (Exception e) {
			e.printStackTrace();
		}		
	}
	
	@Override
	public int loadKeypair(String keypair_name) {
		try {
			
		X509Certificate cert = (X509Certificate)key_store.getCertificate(keypair_name);
		
		if(!cert.getSubjectX500Principal().equals(cert.getIssuerX500Principal())) {
			access.setIssuer(cert.getIssuerX500Principal().getName());
			access.setIssuerSignatureAlgorithm(cert.getSigAlgName());
		}
		access.setVersion(cert.getVersion()-1);//u guiu su za 1 manje verzije kad im se pristupa
		access.setSerialNumber(cert.getSerialNumber().toString());
		access.setNotBefore(cert.getNotBefore());
		access.setNotAfter(cert.getNotAfter());
		access.setPublicKeyAlgorithm(this.getCertPublicKeyAlgorithm(keypair_name));
		access.setPublicKeyDigestAlgorithm(cert.getSigAlgName());
		access.setSubject(this.getSubjectInfo(keypair_name));
		
		if(access.getPublicKeyAlgorithm().equals("EC")) { access.setPublicKeyECCurve(this.getCertPublicKeyParameter(keypair_name));
		access.setPublicKeyParameter(set);
		}
		else access.setPublicKeyParameter(this.getCertPublicKeyParameter(keypair_name));
		
		boolean ian = false;
		boolean bc = false;
		
		Set critSet = cert.getCriticalExtensionOIDs();
		
		if(critSet!=null) {
			if (critSet.contains("2.5.29.19")){
				access.setCritical(Constants.BC, true);
				bc = true;
				
			}
			
			if (critSet.contains("2.5.29.15")) {
				access.setCritical(Constants.KU, true);
				boolean []keyusage = cert.getKeyUsage();
				access.setKeyUsage(keyusage);
			}
	
			
			if (critSet.contains("2.5.29.18")) {
				access.setCritical(Constants.IAN, true);
				ian = true;
				
					}
			
			}//critset
		Set nonCritSet =cert.getNonCriticalExtensionOIDs();//bez keyusage, posto keyusage mora biti kriticna ekstenzija
		
		if(nonCritSet != null) {
			
			if (nonCritSet.contains("2.5.29.18")) {
				ian = true;
			}
			
		
		if (nonCritSet.contains("2.5.29.19")){
			bc= true;
			
		}
		
		}
		
		if (ian) {
			Collection<List<?>> imena = cert.getIssuerAlternativeNames();
			String str=null;
			if (imena!= null) {
				for (List item : imena) {
		            Integer type = (Integer) item.get(0);
		            if (type == 1) {//type 1 je rfc822 name
		            	str = (String) item.get(1);
				
				}
				}
		            
				access.setAlternativeName(Constants.IAN, str);
		
			}
			
		}
		
		if(bc) {
			int i = cert.getBasicConstraints();
			if (i!= -1 ) {
				access.setCA(true);
				access.setPathLen(Integer.toString(i));
			}
			else access.setCA(false);
			
		}
		
		
		
		if (access.isCA()) {
			
			return 2;
		}
		else if(!cert.getSubjectX500Principal().equals(cert.getIssuerX500Principal())){//ako nije self signed, onda je potpisan od strane autoriteta
			
			return 1;
		}
		
		return 0;
		
		}catch (Exception e) {
		e.printStackTrace();
		
	}return -1;
		}
	
	@Override
	public boolean saveKeypair(String keypair_name) {
		try {
		/*if(access.getPublicKeyAlgorithm()!="DSA") {
			GuiInterfaceV1.reportError("Algoritam mora biti DSA!");
			return false;
		}
		*/
		
		if(access.getVersion()==0) {
			GuiInterfaceV1.reportError("Verzija sertifikata mora biti 3!");
			return false;
		}
		
		Enumeration<String>aliases = key_store.aliases();
		while(aliases.hasMoreElements()) {
			if(aliases.nextElement().equals(keypair_name)) {
				GuiInterfaceV1.reportError("Vec postoji par pod tim imenom!");
				return false;
			}
		}
		
		
		KeyPairGenerator generator = KeyPairGenerator.getInstance(access.getPublicKeyAlgorithm(), new BouncyCastleProvider() );
		//Ova sekcija mi je sluzila za testiranje kod prikazivanja parova koji su kriptovani EC algoritmom, trebalo mi je da napravim kljuc
		if(access.getPublicKeyAlgorithm().equals("EC")) {
			String parametri = access.getPublicKeyECCurve();	
			//if(parametri.equals("prime256v1")) {parametri="secp256r1";this.set="X9.62";}
			//else if(parametri.equals("P-256")) {parametri="secp256r1";this.set="NIST";}
			//else if(parametri.equals("P-384")) {parametri="secp384r1";this.set="NIST";}
			//else if(parametri.equals("P-521")) {parametri="secp521r1";this.set="NIST";}
			//else if(parametri.equals("B-283")) {parametri="sect283r1";this.set="NIST";}
			//else if(parametri.equals("B-409")) {parametri="sect409r1";this.set="NIST";}
			//else if(parametri.equals("B-571")) {parametri="sect571r1";this.set="NIST";}
			//else this.set="SEC";
			ECGenParameterSpec ecSpec = new ECGenParameterSpec(parametri);
			generator.initialize(ecSpec);
		}else
		generator.initialize(Integer.parseInt(access.getPublicKeyParameter()));
		KeyPair par = generator.genKeyPair();
		PrivateKey privatni = par.getPrivate();
		PublicKey javni = par.getPublic();
		
		SubjectPublicKeyInfo key_info = SubjectPublicKeyInfo.getInstance(javni.getEncoded());
		
		X500Name subject = new X500Name(access.getSubject());
		BigInteger serial = new BigInteger(access.getSerialNumber());
		Date notBefore = access.getNotBefore();
		Date notAfter = access.getNotAfter();
		
		X509v3CertificateBuilder sertifikat = new X509v3CertificateBuilder(subject,serial,notBefore,notAfter,subject,key_info);
		boolean[]keys=null;
		
		if(access.getKeyUsage()!=null) {
		
		keys = access.getKeyUsage();
		
		KeyUsage ku = new KeyUsage((keys[0] ? KeyUsage.digitalSignature : 0)|(keys[1]? KeyUsage.nonRepudiation : 0)|(keys[2]? KeyUsage.keyEncipherment : 0)
				|(keys[3]?KeyUsage.dataEncipherment:0)|(keys[4]?KeyUsage.keyAgreement:0)|(keys[5]?KeyUsage.keyCertSign:0)|(keys[6]?KeyUsage.cRLSign:0)|(keys[7]?KeyUsage.encipherOnly:0)
				|(keys[8]?KeyUsage.decipherOnly:0));
		sertifikat.addExtension(Extension.keyUsage,access.isCritical(Constants.KU),ku);
		}
		
		if(access.isCA()) {
			String pathlen = access.getPathLen();
			
			if(keys==null) {
				GuiInterfaceV1.reportError("Basic constraints nema smisla ako sertifikat nije CA autoritet i ako ne moze da potpisuje sertifikate!(keyCertSign bit nije selektovan!)");
				return false;
			}
			
			if(!keys[5]){
				GuiInterfaceV1.reportError("Basic constraints nema smisla ako sertifikat nije CA autoritet i ako ne moze da potpisuje sertifikate!(keyCertSign bit nije selektovan!)");
				return false;
			}
			
			
			if(pathlen.equals("")) {
				GuiInterfaceV1.reportError("Path length ne smije biti prazan!");
				return false;
			}
			
			if(Integer.parseInt(pathlen)<0) {
				GuiInterfaceV1.reportError("Path length ne smije biti negativan!");
				return false;
			}
			
			
			BasicConstraints bc;
			bc = new BasicConstraints(Integer.parseInt(pathlen));
			sertifikat.addExtension(Extension.basicConstraints,access.isCritical(Constants.BC),bc);
			}
		
		if(access.getAlternativeName(Constants.IAN)!=null) {
		String[] issuer_alt_names = access.getAlternativeName(Constants.IAN);
		if(issuer_alt_names.length != 0){
			String imena = "";
			boolean first = true;
			for(int i=0;i<issuer_alt_names.length;i++){
				if(first){
					imena += issuer_alt_names[i];//ovo se radi da ne bi stojao zarez ispred prvog imena
					first = false;
				}
				else 
					imena += "," + issuer_alt_names[i];

			}
			
		 
			GeneralName ime = new GeneralName(1,imena);
			GeneralNames names = new GeneralNames(ime);
			sertifikat.addExtension(Extension.issuerAlternativeName, access.isCritical(Constants.IAN), names);
		}
		}
			
			ContentSigner signer = new JcaContentSignerBuilder(access.getPublicKeyDigestAlgorithm()).build(privatni);
			JcaX509CertificateConverter konverter = new JcaX509CertificateConverter();
			X509Certificate cert =  konverter.getCertificate(sertifikat.build(signer));
			
			X509Certificate [] chain = {cert};
			PrivateKeyEntry entry = new PrivateKeyEntry (privatni, chain );
			key_store.setEntry(keypair_name, entry, this.password );
		
			return true;
			
			
		
		
		
		}catch (Exception e) {
			e.printStackTrace();
			
		}return false;
	}

	@Override
	public boolean removeKeypair(String keypair_name) {
		try{
			key_store.deleteEntry(keypair_name);
			return true;
		}catch (KeyStoreException e) {
			e.printStackTrace();
		}
		return false;
	}
	
	
	@Override
	public boolean importKeypair(String keypair_name, String file, String password) {
		File fajl = new File (file);
		try{
			FileInputStream stream = new FileInputStream(fajl);
			KeyStore keyStore = KeyStore.getInstance("PKCS12");
			keyStore.load(stream, password.toCharArray());
			PasswordProtection sif = new PasswordProtection(password.toCharArray());
			Enumeration<String> e = keyStore.aliases();
			String str = e.nextElement();
			
			PrivateKeyEntry ulaz = (PrivateKeyEntry)keyStore.getEntry(str, sif);
			key_store.setEntry(keypair_name, ulaz,sif);
			stream.close();
			return true;
		
		}
		catch(FileNotFoundException e){
			System.out.println("Fajl nije pronadjen!");
			GuiV3.reportError("Fajl nije pronadjen!");
			
		}
		catch(Exception e) {
			e.printStackTrace();
		}
		return false;
	}
	
	
	@Override
	public boolean exportKeypair(String keypair_name, String file, String password) {
		try {
			File out = new File(file);
			KeyStore privremen = KeyStore.getInstance("PKCS12");
			PasswordProtection sif = new PasswordProtection(password.toCharArray());
			PrivateKeyEntry ulaz = (PrivateKeyEntry)key_store.getEntry(keypair_name, this.password);
			//X509Certificate cert = (X509Certificate)key_store.getCertificate(keypair_name);
			if(out.exists()) {
				FileInputStream is = new FileInputStream(out);
				privremen.load(is, password.toCharArray());
				is.close();
			}
			else{
				privremen.load(null);
			}
			FileOutputStream ostream = new FileOutputStream(out);
			privremen.setEntry(keypair_name, ulaz, sif);
			//privremen.setCertificateEntry(keypair_name, cert);
			privremen.store(ostream, password.toCharArray());
			ostream.close();
			return true;
			
			
		}catch (Exception e) {
			e.printStackTrace();
		}
		return false;
	}
	
	@Override
	public boolean importCertificate(String file, String keypair_name) {
		try {
			FileInputStream is = new FileInputStream(file);
			CertificateFactory certfac = CertificateFactory.getInstance("X509");
			Collection<X509Certificate> chain_kol=null;
			chain_kol = (Collection<X509Certificate>) certfac.generateCertificates(is);
			X509Certificate []chain = chain_kol.toArray(new X509Certificate[chain_kol.size()]);
			X509Certificate cert = chain[0];//Ovaj niz se moze iskoristiti za uvozenje svih
			key_store.setCertificateEntry(keypair_name, cert);//sertifikata koji su upisani u fajl
			is.close();
			return true;
			
		}catch(Exception e) {
			e.printStackTrace();
		}
		return false;
	}
	
	@Override
	public boolean exportCertificate(String file, String keypair_name, int encoding, int format) {
	try {
		File out = new File(file);
		Vector<X509Certificate> lanac = new Vector<X509Certificate>();
		X509Certificate []chain=(X509Certificate[])key_store.getCertificateChain(keypair_name);
		X509Certificate cert = (X509Certificate)key_store.getCertificate(keypair_name);
		if(format==1) {
			lanac.addAll(Arrays.asList(chain));
			for(X509Certificate item: lanac) {
				System.out.println(item.getSubjectX500Principal().getName());
			}
		}
		else lanac.add(cert);
		
		if(encoding == 0) {
				FileOutputStream os = new FileOutputStream(out);
				for(X509Certificate item :lanac)
					os.write(item.getEncoded());	
			os.close();
		}
		else {
			JcaPEMWriter pem = new JcaPEMWriter(new FileWriter(out));
			for(X509Certificate item :lanac)
				pem.writeObject(item);
			pem.close();
		}
		return true;
		
		}catch(Exception e) {
			e.printStackTrace();
		}
		return false;
	}
	@Override
	public boolean exportCSR(String file, String keypair_name, String algorithm) {
		try{
			File out = new File (file);
			X509Certificate cert = (X509Certificate)key_store.getCertificate(keypair_name);
			PrivateKeyEntry privatni = (PrivateKeyEntry)key_store.getEntry(keypair_name,password); 
			X500Name x500name = new JcaX509CertificateHolder(cert).getSubject();
			RDN imena[] = x500name.getRDNs();
			AttributeTypeAndValue att=null;
			X500NameStyle stil = RFC4519Style.INSTANCE;
			String common[]= new String[6];
			for(int i=0;i<common.length;i++)common[i]="";
			for (int i=0;i<imena.length;i++) {
				att=imena[i].getTypesAndValues()[0];
				 String s =  stil.oidToDisplayName(att.getType());
				 
				 if(s.equals("c")) common[0]=IETFUtils.valueToString(imena[i].getFirst().getValue());
				 
				 else if(s.equals("st"))common[1]=IETFUtils.valueToString(imena[i].getFirst().getValue());
		         
				 
				 else if(s.equals("l"))common[2]=IETFUtils.valueToString(imena[i].getFirst().getValue());
		         
				 
				 else if(s.equals("o"))common[3]=IETFUtils.valueToString(imena[i].getFirst().getValue());
		         
				 
				 else if(s.equals("ou"))common[4]=IETFUtils.valueToString(imena[i].getFirst().getValue());
		         
				 
				 else if(s.equals("cn"))common[5]=IETFUtils.valueToString(imena[i].getFirst().getValue());
		         
				 
				}
			String argument="";
			int jot = 0;
			if(!(common[0].equals("")))argument+="C="+common[0];
			else if(!(common[1].equals(""))) {argument+="ST="+common[1];jot=1;}
			else if(!(common[2].equals(""))) {argument+="L="+common[2];jot=2;}
			else if(!(common[3].equals(""))) {argument+="O="+common[3];jot=3;}
			else if(!(common[4].equals(""))) {argument+="OU="+common[4];jot=4;}
			else if(!(common[5].equals(""))) {argument+="CN="+common[5];jot=5;}
			switch(jot) {
			case 0: {
				if(!(common[1].equals("")))argument+=",ST="+common[1];
				if(!(common[2].equals("")))argument+=",L="+common[2];
				if(!(common[3].equals("")))argument+=",O="+common[3];
				if(!(common[4].equals("")))argument+=",OU="+common[4];
				argument+=",CN="+common[5];
				break;
			}
			case 1:
			{
				if(!(common[2].equals("")))argument+=",L="+common[2];
				if(!(common[3].equals("")))argument+=",O="+common[3];
				if(!(common[4].equals("")))argument+=",OU="+common[4];
				argument+=",CN="+common[5];
				break;
			}
			case 2:{
				if(!(common[3].equals("")))argument+=",O="+common[3];
				if(!(common[4].equals("")))argument+=",OU="+common[4];
				argument+=",CN="+common[5];
				break;
			}
			case 3:{
				if(!(common[4].equals("")))argument+=",OU="+common[4];
				argument+=",CN="+common[5];
				break;
			}
			case 4:{
				argument+=",CN="+common[5];
				break;
			}
			case 5: {
				break;
			}
			}
			
			PKCS10CertificationRequestBuilder bilder = new JcaPKCS10CertificationRequestBuilder( new X500Principal(argument),cert.getPublicKey());
			JcaContentSignerBuilder csBuilder = new JcaContentSignerBuilder(algorithm);
			ContentSigner signer = csBuilder.build(privatni.getPrivateKey());
			PKCS10CertificationRequest csr = bilder.build(signer);
			
			JcaPEMWriter pem = new JcaPEMWriter(new FileWriter(out));
			pem.writeObject(csr);
			pem.close();
			return true;
			
		}catch (Exception e) {
			e.printStackTrace();
		}
		
		return false;
	}
	
	
	@Override
	public String importCSR(String file) {
		try{
		FileInputStream input = new FileInputStream (file);
		InputStreamReader citac = new InputStreamReader(input);
		PEMParser pem = new PEMParser(citac);
		Object object = pem.readObject();
		 PKCS10CertificationRequest csr=null;
		 if(object instanceof PKCS10CertificationRequest)
			 csr=(PKCS10CertificationRequest)object;
		 X500Name x500Name = csr.getSubject();
		RDN imena[]=x500Name.getRDNs();
		SubjectPublicKeyInfo pkInfo = csr.getSubjectPublicKeyInfo();
		javniCSR=pkInfo;
		//JcaPEMKeyConverter converter = new JcaPEMKeyConverter();
		//javniCSR = converter.getPublicKey(pkInfo);
		AttributeTypeAndValue att=null;
		
		X500NameStyle stil = RFC4519Style.INSTANCE;
		String common[]= new String[6];
		for(int i=0;i<common.length;i++)common[i]="";
		for (int i=0;i<imena.length;i++) {
			att=imena[i].getTypesAndValues()[0];
			 String s =  stil.oidToDisplayName(att.getType());
			 
			 if(s.equals("c")) common[0]=IETFUtils.valueToString(imena[i].getFirst().getValue());
			 
			 else if(s.equals("st"))common[1]=IETFUtils.valueToString(imena[i].getFirst().getValue());
	         
			 
			 else if(s.equals("l"))common[2]=IETFUtils.valueToString(imena[i].getFirst().getValue());
	         
			 
			 else if(s.equals("o"))common[3]=IETFUtils.valueToString(imena[i].getFirst().getValue());
	         
			 
			 else if(s.equals("ou"))common[4]=IETFUtils.valueToString(imena[i].getFirst().getValue());
	         
			 
			 else if(s.equals("cn"))common[5]=IETFUtils.valueToString(imena[i].getFirst().getValue());
	         
			 
			}
		
		DefaultAlgorithmNameFinder algFinder = new DefaultAlgorithmNameFinder();
		String alg = algFinder.getAlgorithmName(csr.getSignatureAlgorithm());
		if(alg.contains("DSA"))alg="DSA";
		else if(alg.contains("RSA"))alg="RSA";
		else if(alg.contains("EC"))alg="EC";
		
		String argument="";
		int jot = 0;
		if(!(common[0].equals("")))argument+="C="+common[0];
		else if(!(common[1].equals(""))) {argument+="ST="+common[1];jot=1;}
		else if(!(common[2].equals(""))) {argument+="L="+common[2];jot=2;}
		else if(!(common[3].equals(""))) {argument+="O="+common[3];jot=3;}
		else if(!(common[4].equals(""))) {argument+="OU="+common[4];jot=4;}
		else if(!(common[5].equals(""))) {argument+="CN="+common[5];jot=5;}
		switch(jot) {
		case 0: {
			if(!(common[1].equals("")))argument+=",ST="+common[1];
			if(!(common[2].equals("")))argument+=",L="+common[2];
			if(!(common[3].equals("")))argument+=",O="+common[3];
			if(!(common[4].equals("")))argument+=",OU="+common[4];
			argument+=",CN="+common[5];
			break;
		}
		case 1:
		{
			if(!(common[2].equals("")))argument+=",L="+common[2];
			if(!(common[3].equals("")))argument+=",O="+common[3];
			if(!(common[4].equals("")))argument+=",OU="+common[4];
			argument+=",CN="+common[5];
			break;
		}
		case 2:{
			if(!(common[3].equals("")))argument+=",O="+common[3];
			if(!(common[4].equals("")))argument+=",OU="+common[4];
			argument+=",CN="+common[5];
			break;
		}
		case 3:{
			if(!(common[4].equals("")))argument+=",OU="+common[4];
			argument+=",CN="+common[5];
			break;
		}
		case 4:{
			argument+=",CN="+common[5];
			break;
		}
		case 5: {
			break;
		}
		}
		
		citac.close();
		pem.close();
		
		argument+=",SA="+alg;		
		return argument;
		}catch(Exception e) {
			e.printStackTrace();
		}
		return null;
	}
	
	@Override
	public boolean signCSR(String file, String keypair_name, String algorithm) {
		try {
			if(!canSign(keypair_name))return false;
			X509Certificate cert = (X509Certificate)key_store.getCertificate(keypair_name);
			X500Name x500name = new JcaX509CertificateHolder(cert).getSubject();
			RDN rdns[] = x500name.getRDNs();
			char []sifra=password.getPassword();
			AttributeTypeAndValue att=null;
			X500NameStyle stil = RFC4519Style.INSTANCE;
			for(int i=0;i<rdns.length;i++) {
				att=rdns[i].getTypesAndValues()[0];
				String s =  stil.oidToDisplayName(att.getType());
				 if(s.equals("cn")) {s=IETFUtils.valueToString(rdns[i].getFirst().getValue());
				 if (s.equals("ETFrootCA"))sifra="root".toCharArray();break;
				 }
			}
			
			PasswordProtection pass = new PasswordProtection(sifra); 
			PrivateKeyEntry ulaz = (PrivateKeyEntry)key_store.getEntry(keypair_name, pass);
			PrivateKey privatni = ulaz.getPrivateKey();
			X500Name subject = new X500Name(access.getSubject());
			X500Name issuer = new JcaX509CertificateHolder(cert).getSubject();
			//X500Name issuer = new X500Name(cert.getIssuerX500Principal().getName());
			Date notBefore = access.getNotBefore();
			Date notAfter = access.getNotAfter();
			BigInteger serial = new BigInteger(access.getSerialNumber());
			SubjectPublicKeyInfo key_info = javniCSR;
			X509v3CertificateBuilder sertifikat = new X509v3CertificateBuilder(issuer,serial,notBefore,notAfter,subject,key_info);
			
			boolean[]keys=null;
			
			if(access.getKeyUsage()!=null) {
			
			keys = access.getKeyUsage();
			
			KeyUsage ku = new KeyUsage((keys[0] ? KeyUsage.digitalSignature : 0)|(keys[1]? KeyUsage.nonRepudiation : 0)|(keys[2]? KeyUsage.keyEncipherment : 0)
					|(keys[3]?KeyUsage.dataEncipherment:0)|(keys[4]?KeyUsage.keyAgreement:0)|(keys[5]?KeyUsage.keyCertSign:0)|(keys[6]?KeyUsage.cRLSign:0)|(keys[7]?KeyUsage.encipherOnly:0)
					|(keys[8]?KeyUsage.decipherOnly:0));
			sertifikat.addExtension(Extension.keyUsage,access.isCritical(Constants.KU),ku);
			}
			if(access.isCA()) {
			String pathlen = access.getPathLen();
			
			if(keys==null) {
				GuiInterfaceV1.reportError("Basic constraints nema smisla ako sertifikat nije CA autoritet i ako ne moze da potpisuje sertifikate!(keyCertSign bit nije selektovan!)");
				return false;
			}
			
			if(!keys[5]){
				GuiInterfaceV1.reportError("Basic constraints nema smisla ako sertifikat nije CA autoritet i ako ne moze da potpisuje sertifikate!(keyCertSign bit nije selektovan!)");
				return false;
			}
			
			
			if(pathlen.equals("")) {
				GuiInterfaceV1.reportError("Path length ne smije biti prazan!");
				return false;
			}
			
			if(Integer.parseInt(pathlen)<0) {
				GuiInterfaceV1.reportError("Path length ne smije biti negativan!");
				return false;
			}
			
			
			BasicConstraints bc;
			bc = new BasicConstraints(Integer.parseInt(pathlen));
			sertifikat.addExtension(Extension.basicConstraints,access.isCritical(Constants.BC),bc);
			}
			
			if(access.getAlternativeName(Constants.IAN)!=null) {
			String[] issuer_alt_names = access.getAlternativeName(Constants.IAN);
			if(issuer_alt_names.length != 0){
				String imena = "";
				boolean first = true;
				for(int i=0;i<issuer_alt_names.length;i++){
					if(first){
						imena += issuer_alt_names[i];//ovo se radi da ne bi stojao zarez ispred prvog imena
						first = false;
					}
					else 
						imena += "," + issuer_alt_names[i];

				}
			
				GeneralName ime = new GeneralName(1,imena);
				GeneralNames names = new GeneralNames(ime);
				sertifikat.addExtension(Extension.issuerAlternativeName, access.isCritical(Constants.IAN), names);
			}
			}
			
			
			ContentSigner signer = new JcaContentSignerBuilder(algorithm).build(privatni);
			JcaPEMWriter writer = new JcaPEMWriter(new FileWriter(file));
			JcaX509CertificateConverter konverter = new JcaX509CertificateConverter();
			X509Certificate signed =  konverter.getCertificate(sertifikat.build(signer));//izrada sertifikata koji je potpisan
			
			
			X509Certificate []chain1 = (X509Certificate[])key_store.getCertificateChain(keypair_name);//dohvatanje lanca sertifikata
			Vector<X509Certificate> vector = new Vector<X509Certificate>();
			vector.add(signed);
			vector.addAll(Arrays.asList(chain1)); 
			
			X509Certificate []chain = (X509Certificate[])vector.toArray(new X509Certificate[vector.size()]);
			
			
			//ispis u pkcs7 formatu
			CMSSignedDataGenerator generator = new CMSSignedDataGenerator();
			generator.addSignerInfoGenerator(new JcaSignerInfoGeneratorBuilder(new JcaDigestCalculatorProviderBuilder()
                    .setProvider("BC").build()).build(signer, signed));
			List<X509Certificate> certList = new ArrayList<X509Certificate>();
			certList.addAll(Arrays.asList(chain));
			Store certs = new JcaCertStore(certList);
			generator.addCertificates(certs);
			CMSTypedData content = new CMSProcessableByteArray(signed.getEncoded());
			CMSSignedData signedData = generator.generate(content, true);
			ContentInfo ci = signedData.toASN1Structure();
			writer.writeObject(ci);
			writer.close();
			return true;
			
			
		}catch(Exception e) {
			e.printStackTrace();
		}
		return false;
	}
	
	
	
	@Override
	public boolean importCAReply(String file, String keypair_name) {
		try {
			FileInputStream is = new FileInputStream(file);
			X509Certificate local = (X509Certificate)key_store.getCertificate(keypair_name);
			CertificateFactory certfac = CertificateFactory.getInstance("X.509");
			Collection c = certfac.generateCertificates(is);
			X509Certificate cert=null;
			X509Certificate issuer=null;
			Iterator iter = c.iterator();
			Vector<X509Certificate> vector = new Vector<X509Certificate>();
			while(iter.hasNext()) {
			vector.add((X509Certificate)iter.next());
			}
			cert = vector.get(0);
			issuer = vector.get(1);
			if(!(cert.getPublicKey().equals(local.getPublicKey()))) {
				GuiInterfaceV1.reportError("Nije odgovarajuci CA Reply!");
				return false;
			}
			X509Certificate []chain = (X509Certificate[])vector.toArray(new X509Certificate[vector.size()]);
			if(!cert.getIssuerX500Principal().equals(issuer.getSubjectX500Principal())) {
				System.out.println("Ne valja");
			}
			PrivateKeyEntry entry = (PrivateKeyEntry)key_store.getEntry(keypair_name, password);
			PrivateKey privatni =entry.getPrivateKey();
			this.removeKeypair(keypair_name);
			key_store.setKeyEntry(keypair_name, privatni,password.getPassword() , chain);
			
			
			X509Certificate []lanac = (X509Certificate[])key_store.getCertificateChain(keypair_name);
			for(int i = 0; i <lanac.length;i++) {
				System.out.println(lanac[i].getSubjectX500Principal().getName());
			}
			
			this.loadKeypair(keypair_name);
			
			
			return true;
			
			
		}catch(Exception e) {
			e.printStackTrace();
		}
		return false;
	}
	
	
	
	@Override
	public boolean canSign(String keypair_name) {
		try{
			X509Certificate cert = (X509Certificate)key_store.getCertificate(keypair_name);
			Set critSet = cert.getCriticalExtensionOIDs();
			if (critSet!=null) {
				if(critSet.contains("2.5.29.19")&&critSet.contains("2.5.29.15")) {
					boolean[] keyusage = cert.getKeyUsage();
					if (keyusage[5]==true)
					return true;
				}
			}
			return false;
		}catch (KeyStoreException e) {
			e.printStackTrace();
		}
		
		
		return false;
	}
	
	@Override
	public String getSubjectInfo(String keypair_name) {
		try{
			X509Certificate cert = (X509Certificate)key_store.getCertificate(keypair_name);
		
		String str = cert.getSubjectX500Principal().getName();
		String alg = cert.getPublicKey().getAlgorithm();
		str+=",SA="+alg;
		return str;
		}catch (KeyStoreException e) {
			e.printStackTrace();
		}
		
		return null;
	}
	
	@Override
	public String getCertPublicKeyAlgorithm(String keypair_name) {
		try {
			X509Certificate cert = (X509Certificate)key_store.getCertificate(keypair_name);
			return cert.getPublicKey().getAlgorithm();
			
		}catch (KeyStoreException e) {
			e.printStackTrace();
		}
		return null;
	}
	
	@Override
	public String getCertPublicKeyParameter(String keypair_name) {
		try {
			X509Certificate cert = (X509Certificate)key_store.getCertificate(keypair_name);
			String str = cert.getPublicKey().getAlgorithm();
			String povratna = null;
			if(str.equals("DSA")) {
				int length = ((DSAPublicKey)cert.getPublicKey()).getY().bitLength();
				if(length<=1024)length=1024;
				else length=2048;
				povratna=Integer.toString(length);
			}
			else if(str.equals("RSA")) {
				int length = ((RSAPublicKey)cert.getPublicKey()).getModulus().bitLength();
				if(length<=1024)length=1024;
				else if(length<=2048)length=2048;
				else if(length<=4096)length=4096;
				povratna=Integer.toString(length);
			}
			else if(str.equals("EC")) {
				 ECPublicKey kljuc = (ECPublicKey)cert.getPublicKey();
				 
				 byte[] enc = kljuc.getEncoded(); 
				    SubjectPublicKeyInfo info = SubjectPublicKeyInfo.getInstance(ASN1Sequence.getInstance(enc));
				    AlgorithmIdentifier alg = info.getAlgorithm();
				    ASN1ObjectIdentifier oid = (ASN1ObjectIdentifier) alg.getParameters();
				    povratna=oid.toString();
				    if(povratna.equals("1.2.840.10045.3.1.7")){povratna="prime256v1";this.set="X9.62";}
				    else if(povratna.equals("1.3.132.0.39")) {povratna="B-571";this.set="NIST";}
				    else if(povratna.equals("1.3.132.0.37")) {povratna="B-409";this.set="NIST";}
				    else if(povratna.equals("1.3.132.0.17")) {povratna="B-283";this.set="NIST";}
				    else if(povratna.equals("1.3.132.0.35")) {povratna="P-521";this.set="NIST";}
				    else if(povratna.equals("1.3.132.0.34")) {povratna="P-384";this.set="NIST";}
				    else if(povratna.equals("1.3.132.0.10")) {povratna="secp256k1";this.set="SEC";}
				    else if(povratna.equals("1.3.132.0.16")) {povratna="sect283k1";this.set="SEC";}
				    else if(povratna.equals("1.3.132.0.36")) {povratna="sect409k1";this.set="SEC";}
				    else if(povratna.equals("1.3.132.0.38")) {povratna="sect571k1";this.set="SEC";}
				 
			}
			return povratna;
			
		}catch (KeyStoreException e) {
			e.printStackTrace();
		}
		return null;
	}
	
	
	
	public MyCode(boolean[] algorithm_conf, boolean[] extensions_conf, boolean extensions_rules)throws GuiException{
		super (algorithm_conf,extensions_conf,extensions_rules);
		access=super.access;
		password = new PasswordProtection(Integer.toString((new SecureRandom()).nextInt()).toCharArray());
		Security.addProvider(new BouncyCastleProvider());
		
	}


}
