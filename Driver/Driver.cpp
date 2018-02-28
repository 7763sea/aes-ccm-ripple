#include "stdafx.h"
#include <omp.h>
#include <direct.h> 
#include <iostream>
#include <fstream>
using std::cout;
using std::cerr;

#pragma comment(lib, "lib_json.lib")
#include "cryptlib.h"
using CryptoPP::AAD_CHANNEL;
using CryptoPP::DEFAULT_CHANNEL;
using CryptoPP::BufferedTransformation;
// using CryptoPP::AuthenticatedSymmetricCipher;

#include "filters.h"
using CryptoPP::StringSink;
using CryptoPP::StringSource;
using CryptoPP::AuthenticatedEncryptionFilter;
using CryptoPP::AuthenticatedDecryptionFilter;
#include <math.h>
#include "aes.h"
using CryptoPP::AES;

#include "ccm.h"
using CryptoPP::CCM;
#include "io.h"
#include "hex.h"
using CryptoPP::HexEncoder;

using namespace std;
#include <cassert>
#include "json/json.h"
#include "assert.h"
static const char encode_map[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
static char decode_map[256];
#define MAX_PATH 1024  //最长路径长度 
//#define MY
#define MYNO
//#define PRINT
static void initBase64DecodeMap()
{
	memset(decode_map,-1,sizeof(decode_map));
	for (int i = 'A'; i <= 'Z'; ++i) decode_map[i] = 0 + (i - 'A');
	for (int i = 'a'; i <= 'z'; ++i) decode_map[i] = 26 + (i - 'a');
	for (int i = '0'; i <= '9'; ++i) decode_map[i] = 52 + (i - '0');
	decode_map[(unsigned char)'+'] = 62;
	decode_map[(unsigned char)'/'] = 63;
	decode_map[(unsigned char)'='] = 0;
}

bool CBase64::Encode(const string& strIn,string& strOut)
{
	size_t nInLen = strIn.length();
	size_t numOrig24BitValues = nInLen/3;
	bool havePadding = (nInLen != numOrig24BitValues*3);
	bool havePadding2 = (nInLen == numOrig24BitValues*3 + 1);
	size_t numResultBytes = 4*(numOrig24BitValues + havePadding);
	strOut.clear();
	for (size_t i = 0; i < numOrig24BitValues; ++i)
	{
		strOut.append(1,encode_map[(strIn[3*i] >> 2) & 0x3F]);
		strOut.append(1,encode_map[((strIn[3*i] << 4) & 0x30) | ((strIn[3*i+1] >> 4) & 0x0F)]);
		strOut.append(1,encode_map[((strIn[3*i+1] << 2) & 0x3C) | ((strIn[3*i+2] >> 6) & 0x03)]);
		strOut.append(1,encode_map[strIn[3*i+2] & 0x3F]);

	}

	if (havePadding)
	{
		size_t i = numOrig24BitValues;
		strOut.append(1,encode_map[(strIn[3*i] >> 2) & 0x3F]);
		if (havePadding2)
		{
			strOut.append(1,encode_map[((strIn[3*i] << 4) & 0x30) | ((strIn[3*i+1] >> 4) & 0x0F)]);
			strOut.append(1,'=');
		}
		else
		{
			strOut.append(1,encode_map[((strIn[3*i] << 4) & 0x30) | ((strIn[3*i+1] >> 4) & 0x0F)]);
			strOut.append(1,encode_map[((strIn[3*i+1] << 2) & 0x3C) | ((strIn[3*i+2] >> 6) & 0x03)]);
		}
		strOut.append(1,'=');
	}

	return true;
}

bool CBase64::Decode(const string& strIn,string& strOut,bool fCheckInputValid/* = false*/)
{
	size_t nInlen = strIn.length();
	if (nInlen < 4 || (nInlen % 4) != 0)
	{
		return false;
	}

	static bool bInit = false;
	if (!bInit)
	{
		initBase64DecodeMap();
		bInit = true;
	}

	if (fCheckInputValid)
	{
		for (size_t i = 0; i < nInlen; ++i)
		{
			if (decode_map[(unsigned char)strIn[i]] == -1)
			{
				return false;
			}
		}
	}
	size_t nOutLen = (nInlen * 3) / 4;
	string strTmpOut;
	strTmpOut.resize(nOutLen);
	size_t nLoopLen = nOutLen / 3;
	for (size_t i = 0; i < nLoopLen;++i)
	{
		strTmpOut[i*3] = ((decode_map[strIn[i*4]] << 2) & 0xFC) | ((decode_map[strIn[i*4+1]] >> 4) & 0x03);
		strTmpOut[i*3+1] = ((decode_map[strIn[i*4+1]] << 4) & 0xF0) | ((decode_map[strIn[i*4+2]] >> 2) & 0x0F);
		strTmpOut[i*3+2] = ((decode_map[strIn[i*4+2]] << 6) & 0xC0) | (decode_map[strIn[i*4+3]] & 0x3F);
	}

	if (strIn[nInlen - 1] == '=')
	{
		nOutLen--;
		if (strIn[nInlen - 2] == '=')
		{
			nOutLen--;
		}
	}
	const char* pData = strTmpOut.data();
	strOut.clear();
	strOut.append(pData,pData + nOutLen);
	return true;
}

bool CBase64::myDecode(const string& ctx,string& strOut)
{
	byte key[] = {0x31,0x27,0xF2,0x30,0xA7,0xC3,0xA8,0xA0,0x6F,0x57,0xBF,0xF6,0xD9,0x91,0xC5,0xA3,0xCD,0xBB,0xBC,0xCB,0xB8,0x70,0xE3,0xE7,0xC4,0x1D,0x4B,0x34,0x70,0x6B,0x62,0xA8};

	// byte iv[]={ 0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b };
	byte iv[]={0x2B,0x44,0x4B,0xA9,0xB6,0x95,0x1E,0xC5,0x0D,0x08,0x4C,0x37,0x07 };

	const byte aa[] = { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
		0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x11,0x12,0x13 };
	string adata = string( (const char*)aa, sizeof(aa) );
	adata = "";
	const byte pa[] = { 0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,
		0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
		0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37 };

	string pdata = string( (const char*)pa, sizeof(pa) );
	pdata = "{\"masterkey\":\"shPLmjWXmhpiFd7AFhh2rAmQTVLMj\",\"account_id\":\"r9us1jJnvg9LK9wF1DTUWJc4qpp7GVENm8\",\"contacts\":[],\"created\":\"2017-08-23T19:01:44.475Z\"}";
	const int TAG_SIZE = 8;
	// Recovered
	string cipher,radata, rpdata;
	// Break the cipher text out into it's
	//  components: Encrypted and MAC

	CBase64::Decode(ctx,cipher,true);
	string enc = cipher.substr( 0, cipher.length()-TAG_SIZE );
	string tag = cipher.substr( cipher.length()-TAG_SIZE );

	// Sanity checks
	assert( cipher.size() == enc.size() + tag.size() );
	assert( enc.size() == pdata.size() );
	assert( TAG_SIZE == tag.size() );

	// Not recovered - sent via clear channel
	radata = adata;

	CCM< AES, TAG_SIZE >::Decryption d;
	d.SetKeyWithIV( key, sizeof(key), iv, sizeof(iv) );
	d.SpecifyDataLengths( radata.size(), enc.size(), 0 );

	// Object will not throw an exception
	//  during decryption\verification _if_
	//  verification fails.
	//AuthenticatedDecryptionFilter df( d, NULL,
	// AuthenticatedDecryptionFilter::MAC_AT_BEGIN );

	AuthenticatedDecryptionFilter df( d, NULL,
		AuthenticatedDecryptionFilter::MAC_AT_BEGIN | 
		AuthenticatedDecryptionFilter::THROW_EXCEPTION );

	// The order of the following calls are important
	df.ChannelPut( DEFAULT_CHANNEL, (const byte*)tag.data(), tag.size() );
	df.ChannelPut( AAD_CHANNEL, (const byte*)adata.data(), adata.size() );
	df.ChannelPut( DEFAULT_CHANNEL, (const byte*)enc.data(), enc.size() );

	df.ChannelMessageEnd( AAD_CHANNEL );
	df.ChannelMessageEnd( DEFAULT_CHANNEL );

	// If the object does not throw, here's the only
	// opportunity to check the data's integrity
	bool b = false;
	b = df.GetLastResult();
	assert( true == b );

	// Remove data from channel
	string retrieved;
	size_t n = (size_t)-1;

	// Plain text recovered from enc.data()
	df.SetRetrievalChannel( DEFAULT_CHANNEL );
	n = (size_t)df.MaxRetrievable();
	retrieved.resize( n );

	if( n > 0 ) { df.Get( (byte*)retrieved.data(), n ); }
	rpdata = retrieved;
	strOut = retrieved;
	if( rpdata == pdata )
	{
		return true;
	};

	return false;

}

bool CBase64::byteDecode(const string& ctx,string& strOut,byte key[],int key_size,byte iv[],int iv_size)
{

	byte key_my[] = {0x31,0x27,0xF2,0x30,0xA7,0xC3,0xA8,0xA0,0x6F,0x57,0xBF,0xF6,0xD9,0x91,0xC5,0xA3,0xCD,0xBB,0xBC,0xCB,0xB8,0x70,0xE3,0xE7,0xC4,0x1D,0x4B,0x34,0x70,0x6B,0x62,0xA8};

	// byte iv[]={ 0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b };
	byte iv_my[]={0x2B,0x44,0x4B,0xA9,0xB6,0x95,0x1E,0xC5,0x0D,0x08,0x4C,0x37,0x07 };


	const byte aa[] = { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
		0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x11,0x12,0x13 };
	string adata = string( (const char*)aa, sizeof(aa) );
	adata = "";
	const byte pa[] = { 0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,
		0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
		0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37 };

	string pdata = string( (const char*)pa, sizeof(pa) );
	pdata = "{\"masterkey\":\"shPLmjWXmhpiFd7AFhh2rAmQTVLMj\",\"account_id\":\"r9us1jJnvg9LK9wF1DTUWJc4qpp7GVENm8\",\"contacts\":[],\"created\":\"2017-08-23T19:01:44.475Z\"}";
	const int TAG_SIZE = 8;
	// Recovered
	string cipher,radata, rpdata;
	// Break the cipher text out into it's
	//  components: Encrypted and MAC

	CBase64::Decode(ctx,cipher,true);
	string enc = cipher.substr( 0, cipher.length()-TAG_SIZE );
	string tag = cipher.substr( cipher.length()-TAG_SIZE );

	printf("\r\n this is cipher len is %d \r\n",cipher.length());
	for (int i = 0; i < cipher.length(); i++)
	{
		printf("%#02X,",cipher.c_str()[i]);
	}
	printf("\r\n this is tag\r\n");
		for (int i = 0; i < tag.length(); i++)
	{
		printf("%#02X,",tag.c_str()[i]);
	}
	printf("\r\nthis is tag size: %d\r\n",tag.size());
	// Sanity checks
	assert( cipher.size() == enc.size() + tag.size() );
	//assert( enc.size() == pdata.size() );
	assert( TAG_SIZE == tag.size() );

	// Not recovered - sent via clear channel
	radata = adata;

	CCM< AES, TAG_SIZE >::Decryption d;
	//d.SetKeyWithIV( key_my,sizeof(key_my), iv_my, sizeof(iv_my));
	//d.SetKeyWithIV(key,key_size, iv, iv_size);

	//加入 try catch
	try  
	{  
		d.SetKeyWithIV(key,key_size, iv, iv_size);
	}  
	catch(char *str)  
	{  
		return false;
		cout << str << endl;  
	}  
	catch(int i)  
	{  
		cout << i << endl;  
	}  
	d.SpecifyDataLengths(radata.size(), enc.size(), 0 );

	// Object will not throw an exception
	//  during decryption\verification _if_
	//  verification fails.
	//AuthenticatedDecryptionFilter df( d, NULL,
	// AuthenticatedDecryptionFilter::MAC_AT_BEGIN );

	AuthenticatedDecryptionFilter df( d, NULL,
		AuthenticatedDecryptionFilter::MAC_AT_BEGIN | 
		AuthenticatedDecryptionFilter::THROW_EXCEPTION );

	// The order of the following calls are important
	df.ChannelPut( DEFAULT_CHANNEL, (const byte*)tag.data(), tag.size() );
	df.ChannelPut( AAD_CHANNEL, (const byte*)adata.data(), adata.size() );
	printf("adata.data() size is %d \r\n",adata.size());
	for (int i = 0; i < adata.size(); i++)
	{
		printf("%#02X \r\n",adata.data()[i]);
	}
	df.ChannelPut( DEFAULT_CHANNEL, (const byte*)enc.data(), enc.size() );

	df.ChannelMessageEnd( AAD_CHANNEL );
	try{
		df.ChannelMessageEnd( DEFAULT_CHANNEL );
	}  
	catch(char *str)  
	{  
		cout << str << endl;
		return false;

	}  
	catch(int i)  
	{  
		cout << i << endl;  
	}  


	// If the object does not throw, here's the only
	// opportunity to check the data's integrity
	bool b = false;
	try
	{
		b = df.GetLastResult();
		if(!b)
		{
			return b;
		}
		assert( true == b );

	}  
	catch(char *str)  
	{  
		return false;
		cout << str << endl;  
	}  
	catch(int i)  
	{  
		cout << i << endl;  
	}  


	// Remove data from channel
	string retrieved;
	size_t n = (size_t)-1;

	// Plain text recovered from enc.data()
	try{
		df.SetRetrievalChannel( DEFAULT_CHANNEL );

	}  
	catch(char *str)  
	{  
		return false;
		cout << str << endl;  
	}  
	catch(int i)  
	{  
		cout << i << endl;  
	}  
	n = (size_t)df.MaxRetrievable();
	retrieved.resize( n );

	if( n > 0 ) { df.Get( (byte*)retrieved.data(), n ); }
	rpdata = retrieved;
	strOut = retrieved;
	if( rpdata [0]=='{' )
	{
		return true;
	};
	if( rpdata == pdata )
	{
		return true;
	};

	return false;

}

bool CBase64::PassGen(int legth,int mod,char*& out)
{
	char num[] = {'0','1','2','3','4','5','6','7','8','9'};
	char uper[] = {'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z'};
	char lower[] = {'a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z'};

	char *pass = new char[legth];
	switch (mod)
	{
	case 0:
		//only num
		break;
	case 1:
		//only uper
		break;
	case 2:
		//only lower
		break;
	case 3:
		//only num+uper
	case 4:
		//only num+lower
	case 5:
		//only uper+lower
	case 6:
		// num+uper+lower
		break;

	default:
		break;
	}


	return false;
}

int CBase64::ComputeNonce(int iv_length,int ct_bytes_length)
{

	ct_bytes_length = ct_bytes_length - 8;
	int l = 2;

	while (l < 4 && (((unsigned int)ct_bytes_length) >> 8 * l) != 0)
	{
		l++;
	}

	if (l < 15 - iv_length)
	{
		l = 15 - iv_length;
	}

	int newLength = 15 - l;

	printf("this is Nonce len %d \r\n",newLength);
	return newLength;
}
int CBase64::GetAllgpxFilepathFromfolder(char*  Path,std::vector<std::string> &fileList)
{
	char szFind[MAX_PATH];
	WIN32_FIND_DATA FindFileData;
	strcpy(szFind,Path);
	strcat(szFind,"\\*.*");
	HANDLE hFind=FindFirstFile(szFind,&FindFileData);
	if(INVALID_HANDLE_VALUE == hFind)   
		return -1;

	do
	{
		if(FindFileData.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY)
		{
			if(strcmp(FindFileData.cFileName,".")!=0 && strcmp(FindFileData.cFileName, "..")!=0)
			{
				//发现子目录，递归之
				char szFile[MAX_PATH] = {0};
				strcpy(szFile,Path);
				strcat(szFile,"\\");
				strcat(szFile,FindFileData.cFileName);
				GetAllgpxFilepathFromfolder(szFile,fileList);
			}
		}
		else
		{
			fileList.push_back( FindFileData.cFileName);
			//找到文件，处理之
			std::cout << "" << "\\" << FindFileData.cFileName << std::endl;
		}
	}while(FindNextFile(hFind,&FindFileData));

	FindClose(hFind);

	return 0;
}

int CheckDir(char* Dir)  
{  
	//this function #include <direct.h><memeory><stdlib.h><stdlio.h>  
	//检查文件夹是否存在，不存在则创建之  
	//文件夹存在返回0，  
	//文件夹创建失败返回-1  
	//文件夹创建失败返回1  

	FILE *fp = NULL;  
	char TempDir[200];  
	memset(TempDir,'\0',sizeof(TempDir));  
	sprintf(TempDir,Dir);  
	strcat(TempDir,"\\");  
	fp=fopen(TempDir,"w");  
	if (!fp)  
	{  
		if (_mkdir(Dir)==0)  
		{  
			return 1;  
		}  
		else  
		{  
			return -1;  
		}  
	}  
	else  
	{  
		fclose(fp);  
	}  
	return 0;  

	//main's test sentence    
	//char *filePath="G:\\project\\divGraph\\divGraph\\img2";  
	//CheckDir(filePath);  
}  

int main(int argc, char* argv[])
{
	LARGE_INTEGER freq;
	LARGE_INTEGER strt;
	LARGE_INTEGER ed;
	QueryPerformanceFrequency(&freq);
	QueryPerformanceCounter(&strt);

	// Test Vector 003
	// byte key[]={ 0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,
	//			 0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f };
	byte key[] = {0x31,0x27,0xF2,0x30,0xA7,0xC3,0xA8,0xA0,0x6F,0x57,0xBF,0xF6,0xD9,0x91,0xC5,0xA3,0xCD,0xBB,0xBC,0xCB,0xB8,0x70,0xE3,0xE7,0xC4,0x1D,0x4B,0x34,0x70,0x6B,0x62,0xA8};

	// byte iv[]={ 0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b };
	byte iv[]={0x2B,0x44,0x4B,0xA9,0xB6,0x95,0x1E,0xC5,0x0D,0x08,0x4C,0x37,0x07 };

	const byte aa[] = { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
		0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x11,0x12,0x13 };
	string adata = string( (const char*)aa, sizeof(aa) );
	adata = "";
	const byte pa[] = { 0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,
		0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
		0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37 };

	string pdata = string( (const char*)pa, sizeof(pa) );
	pdata = "{\"masterkey\":\"shPLmjWXmhpiFd7AFhh2rAmQTVLMj\",\"account_id\":\"r9us1jJnvg9LK9wF1DTUWJc4qpp7GVENm8\",\"contacts\":[],\"created\":\"2017-08-23T19:01:44.475Z\"}";
	const int TAG_SIZE = 8;

	//CTX e3b201a9f5b71a7a9b1ceaeccd97e70b6176aad9a4428aa5
	//TAG 484392fbc1b09951

	//0xE3 0x9D 0x42 0x30 0xF7 0x53 0xEB 0x2B 0xE4 0xC3 0x6B 0x02 0x5C 0xD7 0x65 0xD6 0xC1 0xC8 0x6D 0xE5 0x6D 0x00 0x4D 0x1E 0xA8 0x1F 0x62 0x3E 0x42 0x09 0x96 0x12 0x05 0xB3 0xBF 0x49 0x36 0x51 0x7F 0xE7 0xCB 0x50 0x29 0xA8 0x05 0xFF 0xAD 0x2C 0xAA 0xA6 0xA9 0xFF 0xB5 0xC7 0xE1 0x2E 0x20 0x0A 0x30 0x11 0x59 0x58 0x7D 0x0E 0x09 0x6E 0xDF 0x6E 0x37 0x2E 0x8D 0xCC 0xB2 0xA2 0x47 0x8D 0x1B 0x4B 0x36 0xCE 0xA1 0xF0 0x56 0x45 0x4E 0xB3 0xA5 0x6E 0xE2 0x30 0x47 0xD2 0xDB 0xF6 0x16 0xE5 0x5D 0x88 0x32 0x0F 0x70 0xF1 0x4B 0xA1 0xA5 0x6D 0xF9 0x81 0x4C 0xB2 0xCA 0x62 0x1B 0xB9 0xE9 0x02 0xC5 0x34 0xA7 0x00 0xD0 0xD0 0xAE 0xC9 0xEB 0x12 0x02 0xBF 0xE9 0x36 0x5D 0xCE 0xD4 0xA0 0x4C 0xB3 0xB9 0x52 0x0E 0x42 0xD7 0xA6 0x2B 0x43 0x0D 0x0C 0x73 0xBD 0x0E 0xB4 0xBF 0xE6 0x93 0x02

	//E39D4230F753EB2BE4C36B025CD765D6C1C86DE56D004D1EA81F623E4209961205B3BF4936517FE7CB5029A805FFAD2CAAA6A9FFB5C7E12E200A301159587D0E096EDF6E372E8DCCB2A2478D1B4B36CEA1F056454EB3A56EE23047D2DBF616E55D88320F70F14BA1A56DF9814CB2CA621BB9E902C534A700D0D0AEC9EB1202BFE9365DCED4A04CB3B9520E42D7A62B430D0C73BD0EB4BFE69302
	// Encrypted, with Tag
	string cipher, encoded,ctx;
	ctx = "451CMPdT6yvkw2sCXNdl1sHIbeVtAE0eqB9iPkIJlhIFs79JNlF/58tQKagF/60sqqap/7XH4S4gCjARWVh9Dglu3243Lo3MsqJHjRtLNs6h8FZFTrOlbuIwR9Lb9hblXYgyD3DxS6GlbfmBTLLKYhu56QLFNKcA0NCuyesSAr/pNl3O1KBMs7lSDkLXpitDDQxzvQ60v+aTAg==";
	// Recovered
	string radata, rpdata,outdata;


	ifstream file;
	char output[8192];
	int x;

	file.open("../wallet.txt");

	file>>output;	
#ifdef PRINT

	cout <<"this is file info:"<< output<<endl;
#endif
	string mycipher =output ;
	CBase64::Decode(output,mycipher);

	Json::Reader reader;  
	Json::Value root;  
	char* myct = NULL;
	std::string json_ct,myiv;
	if (reader.parse(mycipher, root))  // reader将Json字符串解析到root，root将包含Json里所有子元素  
	{  
		json_ct = root["ct"].asString();  // 访问节点，upload_id = "UP000000"  
		CBase64::Decode(root["iv"].asString(),myiv);
#ifdef  PRINT
		cout<<"this is ct info:"<<json_ct<<endl;
		cout<<"this is iv info:"<<root["iv"].asString()<<endl;
#endif

	}  

	const unsigned char *my_iv  =(unsigned char*) myiv.data();

	std::string decode_str_my;
	string testpass = (char*)key;
	CBase64::byteDecode(json_ct,decode_str_my,key,sizeof(key),(byte*)my_iv,CBase64::ComputeNonce(myiv.length(),json_ct.length()));
	cout<< decode_str_my << endl;

	//--------------------------------------------
	char num[] = {'0','1','2','3','4','5','6','7','8','9','\0'};
	char uper[] = {'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z','\0'};
	char lower[] = {'a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z','\0'};
	printf("模式1,跑当前文件夹下pass目录的字典！！！\r\n");
	printf("模式2,debug 信息输出！！！\r\n");
	printf("模式3,跑当指定文件夹下pass目录的字典！！！\r\n");
	if(argc ==2)
	{
		//char  * filePath =".\\base64_pass";
		char  *filePath =".//pass";
		if (argv[1][0]=='3')
		{
			filePath = argv[1];
		}
		if (argv[1][0]=='2')
		{
			std::string ct_str;
			cout<<"this is ct info:"<<json_ct<<endl;
			CBase64::Decode(root["ct"].asString(),ct_str);
			const int* ct_byte = (int*)ct_str.c_str();
			printf("this i want : [%d,%d,%d,%d] [%#x,%#x,%#x,%#x]\r\n",ct_byte[0],ct_byte[1],ct_byte[2],ct_byte[3],ct_byte[0],ct_byte[1],ct_byte[2],ct_byte[3]);
		}

		///枚举目录文件
		vector<string> files;  

		////获取该路径下的所有文件  
		CBase64::GetAllgpxFilepathFromfolder(filePath,files);

		char str[30];  
		int size = files.size();  
		for (int i = 0;i < size;i++)  
		{  
			//cout<<files[i].c_str()<<endl;  
			//逐行读取文件 
			if (argv[1][0]=='1')
			{
				system("cls");
			}
			printf("总文件数量为%d,已经执行的数量为%d,执行的百分比为 %f %\r\n",size,i+1,(i+1)*100.0/size);

			char pass_file_signle [MAX_PATH];
			ifstream infile; 
			sprintf(pass_file_signle,"%s\\%s",filePath,files[i].c_str());
			infile.open(pass_file_signle,std::ifstream::binary);   //将文件流对象与文件连接起来 
			assert(infile.is_open());   //若失败,则输出错误消息,并终止程序运行 

			string s;
			if(1){
				//-----------------新方式
				infile.seekg(0, std::ios::end);    // go to the end  
				int file_length = infile.tellg();           // report location (this is the length)  
				infile.seekg(0, std::ios::beg);  
				char * all_encode_buf = (char *)malloc(file_length);
				infile.read(all_encode_buf,file_length);
				int new_deocde_step = (24)*sizeof(int);

				char  pw_len[4];
				infile.read(pw_len,4);
				int i_pw_len  = int (pw_len[0]);

				for(int i = 0 ;i<file_length/new_deocde_step;i++)
				{
					char * temp  =all_encode_buf+i*new_deocde_step;
					const unsigned char *new_way_ubytepass = (unsigned char  *)(temp+12*4);

					unsigned char endian[32];

					for(int j =0;j<8;j++)
					{
						endian[j*4] =*(new_way_ubytepass+j*4+3);
						endian[j*4+1] = *(new_way_ubytepass+j*4+2); 
						endian[j*4+2] = *(new_way_ubytepass+j*4+1);
						endian[j*4+3] = *(new_way_ubytepass+j*4);
					}
					printf("\r\nkey print \r\n");
					for (int i = 0; i < 8; i++)
					{
						printf("%#02X,%#02X,%#02X,%#02X,",endian[i*4+0],endian[i*4+1],endian[i*4+2],endian[i*4+3]);
					}

					printf("\r\niv print \r\n");
					for (int i = 0; i < 13; i++)
					{
						printf("%#02X,",my_iv[i]);
					}

					char pass_add_end [32];
					memcpy(pass_add_end,temp+4*4,32);
					pass_add_end[0] = '1';
					pass_add_end[31] = '\0';

					bool result = CBase64::byteDecode(json_ct,decode_str_my,(byte *)endian,4*8,(byte*)my_iv,CBase64::ComputeNonce(myiv.length(),json_ct.length()));
					if (argv[1][0]=='2')
					{
						cout<< decode_str_my << endl;
						int * out_decode = (int *)decode_str_my.c_str();
						printf("this is i want out:[%d,%d,%d,%d] [%#x,%#x,%#x,%#x]\r\n",out_decode[0],out_decode[1],out_decode[2],out_decode[3],out_decode[0],out_decode[1],out_decode[2],out_decode[3]);
					}
					if(result)
					{
						ofstream out("crack.txt");
						if(out.is_open())
						{
							out<< "密码已经破解:"<<pass_add_end<<endl;
							out.close();
						}
						cout << "密码已经破解:"<<pass_add_end<<endl;
						return 1;
					}
				}
				free(all_encode_buf);
				infile.close(); 
				//------------------------

			}
			if(0){
				while(getline(infile,s))
				{
					//cout<<s<<endl;
					char *old_info = (char *)s.c_str();
					char * base64pass = strtok(old_info,"|#");
					char *pass_old = strtok(NULL,"|#");
					base64pass = strtok(NULL,"|#");
					string decode_pass;

					CBase64::Decode(base64pass,decode_pass);

					const unsigned char *ubytepass =(const unsigned char*)decode_pass.data();
					bool result = CBase64::byteDecode(json_ct,decode_str_my,(byte *)ubytepass,decode_pass.length(),(byte*)my_iv,CBase64::ComputeNonce(myiv.length(),json_ct.length()));
					if(result)
					{
						cout << "密码已经破解:"<<pass_old<<endl;
						break;
					}
				}
			}
			infile.close();             //关闭文件输入流 
			QueryPerformanceCounter(&ed);
			printf("case only uper 耗时: %d 毫秒\r\n", (ed.QuadPart - strt.QuadPart) * 1000 / freq.QuadPart);
			QueryPerformanceCounter(&strt);
		}
		if (argv[1][0]!='1')
		{
			char done[MAX_PATH];
			sprintf(done,"%s/done",argv[1]);
			CheckDir(done);
		}

	}


	if(argc ==3)
	{
		cout<< "密码长度"<<argv[1]<<"密码组合方式"<<argv[2]<<endl;
		int length = atoi(argv[1]);
		int mod = atoi(argv[2]);
		char *pass = new char[length+1];

		pass[length] ='\0';
		char* combin = NULL;
		switch (mod)
		{
		case 0:
			{
				//初始化
				for (int i = 0; i < length; i++)
				{
					pass[i]='0';
				}
				int combine_len = sizeof(num)/sizeof(char);
				combin = new char[combine_len];

				//数组合并

				memcpy(combin,num,combine_len);
				int test = strlen(combin);
				for (int i = 0; i <pow(combine_len-1, (double)length); i++)
				{
					list<int> yus = list<int>();

					for (int shang = i; shang > 0; shang /=strlen(combin))
					{
						yus.push_back(shang %strlen(combin));
					}
					int j = 0;
					for each(int value in yus)
					{
						pass[length-j-1] = combin[value];
						j++;
					}
					std::string decode_str;
					//cout<< pass << endl;

					char * length_info= new char[10];
					itoa(length,length_info,10);

					int endpass_len = strlen(length_info)+1+length;
					unsigned char* endpass = new unsigned char[endpass_len];
					memcpy(endpass,length_info,strlen(length_info));
					endpass[strlen(length_info)]='|';
					memcpy(endpass+strlen(length_info)+1,pass,length);
					cout<<endpass<<endl;
					CBase64::byteDecode(json_ct,decode_str_my,endpass,endpass_len,(byte*)my_iv,CBase64::ComputeNonce(myiv.length(),json_ct.length()));

					for (int a = 0; a < length; a++)
					{
						pass[a] = '0';
					}
				}
				QueryPerformanceCounter(&ed);
#ifdef  PRINT

				printf("case only num 耗时: %d 毫秒\r\n", (ed.QuadPart - strt.QuadPart) * 1000 / freq.QuadPart);
#endif
				QueryPerformanceCounter(&strt);

			}
			//only num
			break;
		case 1:
			{
				//初始化
				for (int i = 0; i < length; i++)
				{
					pass[i]='A';
				}
				int combine_len = sizeof(uper)/sizeof(char);
				combin = new char[combine_len];

				//数组合并

				memcpy(combin,uper,combine_len);
				int test = strlen(combin);
				for (int i = 0; i <pow(combine_len-1, (double)length); i++)
				{
					list<int> yus = list<int>();

					for (int shang = i; shang > 0; shang /=strlen(combin))
					{
						yus.push_back(shang %strlen(combin));
					}
					int j = 0;
					for each(int value in yus)
					{
						pass[length-j-1] = combin[value];
						j++;
					}
					//cout<< pass << endl;

					for (int a = 0; a < length; a++)
					{
						pass[a] = '0';
					}
				}
			}
			QueryPerformanceCounter(&ed);
#ifdef  PRINT

			printf("case only uper 耗时: %d 毫秒\r\n", (ed.QuadPart - strt.QuadPart) * 1000 / freq.QuadPart);
#endif
			QueryPerformanceCounter(&strt);

			//only uper
			break;
		case 2:
			{
				//初始化
				for (int i = 0; i < length; i++)
				{
					pass[i]='a';
				}
				int combine_len = sizeof(lower)/sizeof(char);
				combin = new char[combine_len];

				//数组合并

				memcpy(combin,lower,combine_len);
				int test = strlen(combin);
				for (int i = 0; i <pow(combine_len-1, (double)length); i++)
				{
					list<int> yus = list<int>();

					for (int shang = i; shang > 0; shang /=strlen(combin))
					{
						yus.push_back(shang %strlen(combin));
					}
					int j = 0;
					for each(int value in yus)
					{
						pass[length-j-1] = combin[value];
						j++;
					}
					//cout<< pass << endl;

					for (int a = 0; a < length; a++)
					{
						pass[a] = '0';
					}
				}
			}
			QueryPerformanceCounter(&ed);
#ifdef  PRINT

			printf("case only lower 耗时: %d 毫秒\r\n", (ed.QuadPart - strt.QuadPart) * 1000 / freq.QuadPart);
#endif
			QueryPerformanceCounter(&strt);

			//only lower
			break;
		case 3:
			{
				//初始化
				for (int i = 0; i < length; i++)
				{
					pass[i]='0';
				}
				int combine_len =  sizeof(num)+sizeof(lower)/sizeof(char)+1;
				combin = new char[combine_len];

				//数组合并

				memcpy(combin,num,combine_len-sizeof(lower)/sizeof(char));
				memcpy(combin+sizeof(num)/sizeof(char)-1,lower,combine_len-sizeof(num)/sizeof(char));
				int test = strlen(combin);
				for (int i = 0; i <pow(combine_len-3, (double)length); i++)
				{
					list<int> yus = list<int>();

					for (int shang = i; shang > 0; shang /=strlen(combin))
					{
						yus.push_back(shang %strlen(combin));
					}
					int j = 0;
					for each(int value in yus)
					{
						pass[length-j-1] = combin[value];
						j++;
					}
					//cout<< pass << endl;

					for (int a = 0; a < length; a++)
					{
						pass[a] = '0';
					}
				}
			}
			QueryPerformanceCounter(&ed);
			printf("case only num+lower 耗时: %d 毫秒\r\n", (ed.QuadPart - strt.QuadPart) * 1000 / freq.QuadPart);
			QueryPerformanceCounter(&strt);

			break;
			//only num+lower
		case 4:
			{
				//初始化
				for (int i = 0; i < length; i++)
				{
					pass[i]='0';
				}
				int combine_len =  sizeof(num)+sizeof(uper)/sizeof(char)+1;
				combin = new char[combine_len];

				//数组合并

				memcpy(combin,num,combine_len-sizeof(uper)/sizeof(char));
				memcpy(combin+sizeof(num)/sizeof(char)-1,uper,combine_len-sizeof(num)/sizeof(char));
				int test = strlen(combin);
				for (int i = 0; i <pow(combine_len-3, (double)length); i++)
				{
					list<int> yus = list<int>();

					for (int shang = i; shang > 0; shang /=strlen(combin))
					{
						yus.push_back(shang %strlen(combin));
					}
					int j = 0;
					for each(int value in yus)
					{
						pass[length-j-1] = combin[value];
						j++;
					}
					//cout<< pass << endl;

					for (int a = 0; a < length; a++)
					{
						pass[a] = '0';
					}
				}
			}
			QueryPerformanceCounter(&ed);
			printf("caseonly num+uper 耗时: %d 毫秒\r\n", (ed.QuadPart - strt.QuadPart) * 1000 / freq.QuadPart);
			QueryPerformanceCounter(&strt);

			break;
			//only num+uper
		case 5:
			{
				//初始化
				for (int i = 0; i < length; i++)
				{
					pass[i]='a';
				}
				int combine_len =  sizeof(lower)+sizeof(uper)/sizeof(char)+1;
				combin = new char[combine_len];

				//数组合并

				memcpy(combin,lower,combine_len-sizeof(uper)/sizeof(char));
				memcpy(combin+sizeof(lower)/sizeof(char)-1,uper,combine_len-sizeof(lower)/sizeof(char));
				int test = strlen(combin);
				for (int i = 0; i <pow(combine_len-3, (double)length); i++)
				{
					list<int> yus = list<int>();

					for (int shang = i; shang > 0; shang /=strlen(combin))
					{
						yus.push_back(shang %strlen(combin));
					}
					int j = 0;
					for each(int value in yus)
					{
						pass[length-j-1] = combin[value];
						j++;
					}
					//cout<< pass << endl;

					for (int a = 0; a < length; a++)
					{
						pass[a] = '0';
					}
				}
			}
			QueryPerformanceCounter(&ed);
			printf("caseonly lower+uper 耗时: %d 毫秒\r\n", (ed.QuadPart - strt.QuadPart) * 1000 / freq.QuadPart);
			QueryPerformanceCounter(&strt);

			break;
			//only lower+uper
		case 6:
			combin = new	char[62];

			// num+uper+lower
			break;

		default:
			break;
		}

	}


	//--------------------------------------------
	file>>x;	
#ifdef PRINT
	cout<<x;			
	cout<<mycipher;
#endif
	file.close();		

#ifdef  MY
#pragma omp parallel for
	for(int idx = 0; idx < 2000000; idx++)
	{
		CBase64::myDecode(ctx,outdata);
	}
	cout << outdata<<endl;

	QueryPerformanceCounter(&ed);
	printf("GPU耗时: %d 毫秒\r\n", (ed.QuadPart - strt.QuadPart) * 1000 / freq.QuadPart);
	QueryPerformanceCounter(&strt);

#endif
#ifdef  MYNO



#endif
	/*********************************\
	\*********************************/

	try
	{
		CCM< AES, TAG_SIZE >::Encryption e;
		e.SetKeyWithIV( key, sizeof(key), iv, sizeof(iv) );
		e.SpecifyDataLengths( adata.size(), pdata.size(), 0 );

		AuthenticatedEncryptionFilter ef( e,
			new StringSink( cipher )
			); // AuthenticatedEncryptionFilter

		// AuthenticatedEncryptionFilter::ChannelPut
		//  defines two channels: DEFAULT_CHANNEL (empty) and AAD_CHANNEL
		//   DEFAULT_CHANNEL is encrypted and authenticated
		//   AAD_CHANNEL is authenticated
		ef.ChannelPut( AAD_CHANNEL, (const byte*)adata.data(), adata.size() );
		ef.ChannelMessageEnd(AAD_CHANNEL);

		// Authenticated data *must* be pushed before
		//  Confidential/Authenticated data
		ef.ChannelPut( DEFAULT_CHANNEL, (const byte*)pdata.data(), pdata.size() );
		ef.ChannelMessageEnd(DEFAULT_CHANNEL);

		// Pretty print
		StringSource( cipher, true,
			new HexEncoder( new StringSink( encoded ), true, 16, " " ) );
	}
	catch( CryptoPP::BufferedTransformation::NoChannelSupport& e )
	{
		// The tag must go in to the default channel:
		//  "unknown: this object doesn't support multiple channels"
		cerr << "Caught NoChannelSupport..." << endl;
		cerr << e.what() << endl;
		cerr << endl;
	}
	catch( CryptoPP::InvalidArgument& e )
	{
		cerr << "Caught InvalidArgument..." << endl;
		cerr << e.what() << endl;
		cerr << endl;
	}

	/*********************************\
	\*********************************/

	// Attack the first and last byte
	//if( cipher.size() > 1 )
	//{
	// cipher[ 0 ] |= 0x0F;
	// cipher[ cipher.size()-1 ] |= 0x0F;
	//}

	/*********************************\
	\*********************************/

	try
	{
		// Break the cipher text out into it's
		//  components: Encrypted and MAC
		string enc = cipher.substr( 0, cipher.length()-TAG_SIZE );
		string tag = cipher.substr( cipher.length()-TAG_SIZE );

		// Sanity checks
		assert( cipher.size() == enc.size() + tag.size() );
		assert( enc.size() == pdata.size() );
		assert( TAG_SIZE == tag.size() );

		// Not recovered - sent via clear channel
		radata = adata;

		CCM< AES, TAG_SIZE >::Decryption d;
		d.SetKeyWithIV( key, sizeof(key), iv, sizeof(iv) );
		d.SpecifyDataLengths( radata.size(), enc.size(), 0 );

		// Object will not throw an exception
		//  during decryption\verification _if_
		//  verification fails.
		//AuthenticatedDecryptionFilter df( d, NULL,
		// AuthenticatedDecryptionFilter::MAC_AT_BEGIN );

		AuthenticatedDecryptionFilter df( d, NULL,
			AuthenticatedDecryptionFilter::MAC_AT_BEGIN | 
			AuthenticatedDecryptionFilter::THROW_EXCEPTION );

		// The order of the following calls are important
		df.ChannelPut( DEFAULT_CHANNEL, (const byte*)tag.data(), tag.size() );
		df.ChannelPut( AAD_CHANNEL, (const byte*)adata.data(), adata.size() );
		df.ChannelPut( DEFAULT_CHANNEL, (const byte*)enc.data(), enc.size() );

		df.ChannelMessageEnd( AAD_CHANNEL );
		df.ChannelMessageEnd( DEFAULT_CHANNEL );

		// If the object does not throw, here's the only
		// opportunity to check the data's integrity
		bool b = false;
		b = df.GetLastResult();
		assert( true == b );

		// Remove data from channel
		string retrieved;
		size_t n = (size_t)-1;

		// Plain text recovered from enc.data()
		df.SetRetrievalChannel( DEFAULT_CHANNEL );
		n = (size_t)df.MaxRetrievable();
		retrieved.resize( n );

		if( n > 0 ) { df.Get( (byte*)retrieved.data(), n ); }
		rpdata = retrieved;
		assert( rpdata == pdata );

#ifdef PRINT
		// All is well - work with data
		cout << "Decrypted and Verified data. Ready for use." << endl;
		cout << endl;

		cout << "adata length: " << adata.size() << endl;
		cout << "pdata length: " << pdata.size() << endl;
		cout << endl;
#endif
		CBase64::Encode(cipher,ctx);

		string test;
		CBase64::Decode(ctx,test);
#ifdef PRINT
		cout << "test: " <<test<< endl;
		cout << "ctx: " <<ctx<< endl;
		cout << "pdata: " << pdata << endl;
		cout << endl;

		cout << "cipher text (enc + tag): " << endl << " " << encoded << endl;
		cout << endl;

		cout << "recovered adata length: " << radata.size() << endl;
		cout << "recovered pdata length: " << rpdata.size() << endl;
		cout << endl;

		//cout << "recovered adata: " << radata << endl;
		cout << "recovered pdata: " << rpdata << endl;
		//cout << endl;
#endif
	}
	catch( CryptoPP::InvalidArgument& e )
	{
		cerr << "Caught InvalidArgument..." << endl;
		cerr << e.what() << endl;
		cerr << endl;
	}
	catch( CryptoPP::HashVerificationFilter::HashVerificationFailed& e )
	{
		cerr << "Caught HashVerificationFailed..." << endl;
		cerr << e.what() << endl;
		cerr << endl;
	}

	/*********************************\
	\*********************************/

	return 0;
}
