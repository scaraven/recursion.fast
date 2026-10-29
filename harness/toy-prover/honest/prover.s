	.file	"toy.c"
	.text
	.p2align 4
	.type	compress, @function
compress:
.LFB78:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rdx, %rax
	negl	%ecx
	shrq	$32, %rax
	xorl	$528734635, %ecx
	xorl	$-1694144372, %eax
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r15
	.cfi_offset 15, -24
	leaq	SIGMA(%rip), %r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	.cfi_offset 14, -32
	.cfi_offset 13, -40
	.cfi_offset 12, -48
	movl	$-1521486534, %r12d
	pushq	%rbx
	andq	$-32, %rsp
	subq	$224, %rsp
	.cfi_offset 3, -56
	vmovdqu	(%rsi), %xmm6
	vmovdqu	16(%rsi), %xmm9
	movq	%fs:40, %r11
	movq	%r11, 216(%rsp)
	movq	%rdi, %r11
	vmovdqu	32(%rsi), %xmm8
	vmovdqu	48(%rsi), %xmm4
	movl	%edx, %esi
	vpsrlw	$8, %xmm9, %xmm1
	vpsrlw	$8, %xmm6, %xmm0
	movl	$-1150833019, %edx
	movl	$1541459225, 40(%rsp)
	vpackuswb	%xmm1, %xmm0, %xmm0
	vpsrlw	$8, %xmm8, %xmm2
	xorl	$1359893119, %esi
	movl	$1779033703, %edi
	vpsrlw	$8, %xmm4, %xmm1
	vpsrlw	$8, %xmm0, %xmm3
	vpackuswb	%xmm1, %xmm2, %xmm2
	vpsrlw	$8, %xmm2, %xmm1
	vpackuswb	%xmm1, %xmm3, %xmm3
	vpcmpeqd	%xmm1, %xmm1, %xmm1
	vpsrlw	$8, %xmm1, %xmm1
	vpmovzxbw	%xmm3, %xmm5
	vpand	%xmm2, %xmm1, %xmm2
	vpand	%xmm9, %xmm1, %xmm9
	vpand	%xmm4, %xmm1, %xmm4
	vpand	%xmm0, %xmm1, %xmm0
	vpand	%xmm6, %xmm1, %xmm6
	vpand	%xmm8, %xmm1, %xmm8
	vpackuswb	%xmm2, %xmm0, %xmm0
	vpackuswb	%xmm9, %xmm6, %xmm6
	vpackuswb	%xmm4, %xmm8, %xmm8
	vpsrlw	$8, %xmm8, %xmm4
	vpsrldq	$8, %xmm0, %xmm2
	vpmovzxbw	%xmm0, %xmm7
	vpsrlw	$8, %xmm6, %xmm0
	vpand	%xmm6, %xmm1, %xmm6
	vpand	%xmm8, %xmm1, %xmm1
	vpackuswb	%xmm4, %xmm0, %xmm0
	vpackuswb	%xmm1, %xmm6, %xmm1
	vpmovzxbw	%xmm2, %xmm2
	vpmovzxbw	%xmm0, %xmm4
	vpsllw	$8, %xmm7, %xmm7
	vpmovzxbw	%xmm1, %xmm8
	vpmovzxwd	%xmm4, %xmm6
	vpsrldq	$8, %xmm4, %xmm4
	vpmovzxwd	%xmm7, %xmm9
	vpslld	$16, %xmm6, %xmm6
	vpsrldq	$8, %xmm7, %xmm7
	vpmovzxwd	%xmm4, %xmm4
	vpor	%xmm9, %xmm6, %xmm6
	vpmovzxwd	%xmm8, %xmm9
	vpmovzxwd	%xmm7, %xmm7
	vpslld	$16, %xmm4, %xmm4
	vpsrldq	$8, %xmm8, %xmm8
	vpor	%xmm9, %xmm6, %xmm6
	vpmovzxwd	%xmm5, %xmm9
	vpsrldq	$8, %xmm5, %xmm5
	vpor	%xmm7, %xmm4, %xmm4
	vpmovzxwd	%xmm8, %xmm8
	vpsrldq	$8, %xmm0, %xmm0
	vpmovzxwd	%xmm5, %xmm5
	vpslld	$24, %xmm5, %xmm5
	vpor	%xmm8, %xmm4, %xmm4
	vpmovzxbw	%xmm0, %xmm0
	vpsllw	$8, %xmm2, %xmm2
	vpsrldq	$8, %xmm1, %xmm1
	vpor	%xmm5, %xmm4, %xmm4
	vmovdqa	%xmm4, 80(%rsp)
	vpmovzxwd	%xmm0, %xmm4
	vpsrldq	$8, %xmm0, %xmm0
	vpmovzxwd	%xmm2, %xmm5
	vpmovzxbw	%xmm1, %xmm1
	vpslld	$16, %xmm4, %xmm4
	vpmovzxwd	%xmm0, %xmm0
	vpsrldq	$8, %xmm2, %xmm2
	vpsrldq	$8, %xmm3, %xmm3
	vpor	%xmm5, %xmm4, %xmm4
	vpmovzxwd	%xmm2, %xmm2
	vpmovzxwd	%xmm1, %xmm5
	vpmovzxbw	%xmm3, %xmm3
	vpslld	$16, %xmm0, %xmm0
	vpsrldq	$8, %xmm1, %xmm1
	vpor	%xmm5, %xmm4, %xmm4
	vpor	%xmm2, %xmm0, %xmm0
	vpmovzxwd	%xmm1, %xmm1
	vmovdqu	(%r11), %ymm2
	vpmovzxwd	%xmm3, %xmm5
	vpslld	$24, %xmm9, %xmm9
	vpslld	$24, %xmm5, %xmm5
	vpor	%xmm1, %xmm0, %xmm0
	vpsrldq	$8, %xmm3, %xmm1
	vpor	%xmm9, %xmm6, %xmm6
	vpor	%xmm5, %xmm4, %xmm4
	vpextrd	$3, %xmm2, 56(%rsp)
	vpmovzxwd	%xmm1, %xmm1
	movl	56(%rsp), %ebx
	vmovdqa	%xmm6, 64(%rsp)
	vpextrd	$2, %xmm2, %r8d
	vpslld	$24, %xmm1, %xmm1
	vmovdqa	%xmm4, 96(%rsp)
	vpextrd	$1, %xmm2, %r13d
	vpor	%xmm1, %xmm0, %xmm0
	vmovd	%xmm2, 60(%rsp)
	vmovdqa	%xmm0, 112(%rsp)
	vextracti128	$0x1, %ymm2, %xmm0
	vpextrd	$1, %xmm0, 44(%rsp)
	vmovd	%xmm0, %r10d
	vpextrd	$3, %xmm0, 36(%rsp)
	movl	%eax, 32(%rsp)
	movq	%r11, 16(%rsp)
	movl	60(%rsp), %r9d
	vpextrd	$2, %xmm0, %r14d
	movl	$1013904242, 28(%rsp)
	.p2align 4
	.p2align 3
.L2:
	movzbl	(%r15), %r11d
	movl	64(%rsp,%r11,4), %eax
	addl	%r10d, %eax
	leal	(%rax,%r9), %r11d
	movzbl	1(%r15), %r9d
	xorl	%r11d, %esi
	movl	64(%rsp,%r9,4), %eax
	rorx	$16, %esi, %esi
	addl	%esi, %edi
	xorl	%edi, %r10d
	rorx	$12, %r10d, %r10d
	addl	%r10d, %eax
	leal	(%rax,%r11), %r9d
	xorl	%r9d, %esi
	rorx	$8, %esi, %esi
	leal	(%rdi,%rsi), %eax
	movzbl	2(%r15), %edi
	movl	%esi, 60(%rsp)
	xorl	%eax, %r10d
	movl	%eax, 56(%rsp)
	movl	32(%rsp), %eax
	rorx	$7, %r10d, %r11d
	movl	%r11d, 24(%rsp)
	movl	44(%rsp), %r11d
	addl	64(%rsp,%rdi,4), %r11d
	movzbl	3(%r15), %r10d
	addl	%r13d, %r11d
	movl	44(%rsp), %edi
	xorl	%r11d, %eax
	movl	64(%rsp,%r10,4), %r13d
	rorx	$16, %eax, %eax
	addl	%eax, %edx
	xorl	%edx, %edi
	rorx	$12, %edi, %edi
	addl	%edi, %r13d
	leal	0(%r13,%r11), %r10d
	xorl	%r10d, %eax
	rorx	$8, %eax, %eax
	leal	(%rdx,%rax), %r13d
	movzbl	4(%r15), %edx
	xorl	%r13d, %edi
	movl	%r13d, 52(%rsp)
	movl	64(%rsp,%rdx,4), %r11d
	movl	28(%rsp), %edx
	rorx	$7, %edi, %edi
	addl	%r14d, %r11d
	addl	%r11d, %r8d
	movzbl	5(%r15), %r11d
	xorl	%r8d, %ecx
	rorx	$16, %ecx, %ecx
	leal	(%rdx,%rcx), %r13d
	xorl	%r13d, %r14d
	rorx	$12, %r14d, %edx
	movl	64(%rsp,%r11,4), %r14d
	addl	%edx, %r14d
	leal	(%r14,%r8), %r11d
	movl	36(%rsp), %r14d
	movl	40(%rsp), %r8d
	xorl	%r11d, %ecx
	rorx	$8, %ecx, %ecx
	addl	%ecx, %r13d
	movl	%ecx, 48(%rsp)
	movzbl	6(%r15), %ecx
	xorl	%r13d, %edx
	addl	64(%rsp,%rcx,4), %r14d
	movl	36(%rsp), %ecx
	rorx	$7, %edx, %edx
	addl	%ebx, %r14d
	movzbl	7(%r15), %ebx
	xorl	%r14d, %r8d
	movl	64(%rsp,%rbx,4), %esi
	rorx	$16, %r8d, %r8d
	addl	%r8d, %r12d
	xorl	%r12d, %ecx
	rorx	$12, %ecx, %ecx
	addl	%ecx, %esi
	leal	(%rsi,%r14), %ebx
	movzbl	8(%r15), %r14d
	xorl	%ebx, %r8d
	rorx	$8, %r8d, %r8d
	addl	%r8d, %r12d
	xorl	%r12d, %ecx
	addl	64(%rsp,%r14,4), %r9d
	movzbl	9(%r15), %r14d
	addl	%edi, %r9d
	rorx	$7, %ecx, %ecx
	xorl	%r9d, %r8d
	addl	64(%rsp,%r14,4), %r9d
	rorx	$16, %r8d, %r8d
	addl	%r8d, %r13d
	xorl	%r13d, %edi
	rorx	$12, %edi, %edi
	addl	%edi, %r9d
	xorl	%r9d, %r8d
	rorx	$8, %r8d, %esi
	movl	%esi, 40(%rsp)
	addl	%r13d, %esi
	xorl	%esi, %edi
	movl	%esi, 28(%rsp)
	movl	60(%rsp), %esi
	rorx	$7, %edi, %edi
	movl	%edi, 44(%rsp)
	movzbl	10(%r15), %edi
	addl	64(%rsp,%rdi,4), %r10d
	leal	(%r10,%rdx), %r13d
	xorl	%r13d, %esi
	rorx	$16, %esi, %esi
	addl	%esi, %r12d
	xorl	%r12d, %edx
	rorx	$12, %edx, %r14d
	movzbl	11(%r15), %edx
	addl	64(%rsp,%rdx,4), %r13d
	movzbl	12(%r15), %edx
	addl	%r14d, %r13d
	addl	64(%rsp,%rdx,4), %r11d
	movl	56(%rsp), %edx
	xorl	%r13d, %esi
	leal	(%r11,%rcx), %r8d
	movl	24(%rsp), %r11d
	rorx	$8, %esi, %esi
	addl	%esi, %r12d
	xorl	%r8d, %eax
	xorl	%r12d, %r14d
	rorx	$16, %eax, %eax
	leal	(%rdx,%rax), %edi
	movzbl	13(%r15), %edx
	movl	%r11d, %r10d
	xorl	%edi, %ecx
	rorx	$7, %r14d, %r14d
	addl	64(%rsp,%rdx,4), %r8d
	rorx	$12, %ecx, %ecx
	addl	%ecx, %r8d
	xorl	%r8d, %eax
	rorx	$8, %eax, %eax
	addl	%eax, %edi
	movl	%eax, 32(%rsp)
	movl	52(%rsp), %eax
	xorl	%edi, %ecx
	rorx	$7, %ecx, %edx
	movl	%edx, 36(%rsp)
	movzbl	14(%r15), %edx
	movl	48(%rsp), %ecx
	addl	64(%rsp,%rdx,4), %ebx
	addl	%r11d, %ebx
	movzbl	15(%r15), %r11d
	xorl	%ebx, %ecx
	rorx	$16, %ecx, %ecx
	leal	(%rax,%rcx), %edx
	addl	64(%rsp,%r11,4), %ebx
	leaq	160+SIGMA(%rip), %rax
	xorl	%edx, %r10d
	rorx	$12, %r10d, %r10d
	addl	%r10d, %ebx
	addq	$16, %r15
	xorl	%ebx, %ecx
	rorx	$8, %ecx, %ecx
	addl	%ecx, %edx
	xorl	%edx, %r10d
	rorx	$7, %r10d, %r10d
	cmpq	%rax, %r15
	jne	.L2
	movl	%r9d, %r15d
	movl	32(%rsp), %eax
	movl	%r13d, %r9d
	movl	28(%rsp), %r13d
	movl	%r15d, 128(%rsp)
	movl	40(%rsp), %r15d
	movl	%eax, 180(%rsp)
	movl	36(%rsp), %eax
	movl	%r15d, 188(%rsp)
	movl	44(%rsp), %r15d
	movl	%r13d, 168(%rsp)
	movq	16(%rsp), %r11
	movl	%r15d, 148(%rsp)
	movl	%r9d, 132(%rsp)
	movl	%esi, 176(%rsp)
	movl	%r12d, 172(%rsp)
	movl	%r14d, 152(%rsp)
	movl	%r8d, 136(%rsp)
	movl	%edi, 160(%rsp)
	movl	%eax, 156(%rsp)
	movl	%ebx, 140(%rsp)
	movl	%ecx, 184(%rsp)
	movl	%edx, 164(%rsp)
	movl	%r10d, 144(%rsp)
	vmovdqa	128(%rsp), %ymm0
	vpxor	160(%rsp), %ymm0, %ymm0
	vpxor	%ymm2, %ymm0, %ymm0
	vmovdqu	%ymm0, (%r11)
	movq	216(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L8
	vzeroupper
	leaq	-40(%rbp), %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L8:
	.cfi_restore_state
	vzeroupper
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE78:
	.size	compress, .-compress
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC1:
	.string	"toy prover: %s\n"
	.text
	.p2align 4
	.type	die, @function
die:
.LFB85:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	popq	%rax
	.cfi_def_cfa_offset 8
	leaq	.LC1(%rip), %rdx
	movl	$2, %esi
	xorl	%eax, %eax
	subq	$8, %rsp
	.cfi_def_cfa_offset 16
	movq	%rdi, %rcx
	movq	stderr(%rip), %rdi
	call	__fprintf_chk@PLT
	movl	$1, %edi
	call	exit@PLT
	.cfi_endproc
.LFE85:
	.size	die, .-die
	.section	.rodata.str1.1
.LC2:
	.string	"out of memory"
	.text
	.p2align 4
	.type	app, @function
app:
.LFB86:
	.cfi_startproc
	pushq	%r13
	.cfi_def_cfa_offset 16
	.cfi_offset 13, -16
	movq	%rsi, %r13
	pushq	%r12
	.cfi_def_cfa_offset 24
	.cfi_offset 12, -24
	movq	%rdx, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 32
	.cfi_offset 6, -32
	movq	%rdi, %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 40
	.cfi_offset 3, -40
	subq	$8, %rsp
	.cfi_def_cfa_offset 48
	movq	8(%rdi), %rax
	movq	(%rdi), %rdi
	leaq	1(%rax,%rdx), %rbx
	movq	%rbx, %rsi
	call	realloc@PLT
	movq	%rax, 0(%rbp)
	testq	%rax, %rax
	je	.L14
	movq	8(%rbp), %rdx
	movq	%r13, %rsi
	cmpq	%rdx, %rbx
	leaq	(%rax,%rdx), %rdi
	cmovb	%rdx, %rbx
	movq	%rbx, %rcx
	subq	%rdx, %rcx
	movq	%r12, %rdx
	call	__memcpy_chk@PLT
	addq	%r12, 8(%rbp)
	addq	$8, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%rbp
	.cfi_def_cfa_offset 24
	popq	%r12
	.cfi_def_cfa_offset 16
	popq	%r13
	.cfi_def_cfa_offset 8
	ret
.L14:
	.cfi_restore_state
	leaq	.LC2(%rip), %rdi
	call	die
	.cfi_endproc
.LFE86:
	.size	app, .-app
	.p2align 4
	.type	app64, @function
app64:
.LFB87:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rdi, %r8
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	andq	$-32, %rsp
	subq	$32, %rsp
	movq	%fs:40, %rax
	movq	%rax, 24(%rsp)
	xorl	%eax, %eax
	movq	%rsp, %rdx
	.p2align 5
	.p2align 4
	.p2align 3
.L16:
	shrx	%rax, %rsi, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L16
	movl	$8, %edx
	movq	%rsp, %rsi
	movq	%r8, %rdi
	call	app
	movq	24(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L21
	leave
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L21:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE87:
	.size	app64, .-app64
	.section	.rodata.str1.1
.LC3:
	.string	"rb"
	.text
	.p2align 4
	.type	readfile, @function
readfile:
.LFB88:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	pushq	%r13
	.cfi_def_cfa_offset 24
	.cfi_offset 13, -24
	pushq	%r12
	.cfi_def_cfa_offset 32
	.cfi_offset 12, -32
	pushq	%rbp
	.cfi_def_cfa_offset 40
	.cfi_offset 6, -40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset 3, -48
	leaq	-65536(%rsp), %r11
	.cfi_def_cfa 11, 65584
.LPSRL0:
	subq	$4096, %rsp
	orq	$0, (%rsp)
	cmpq	%r11, %rsp
	jne	.LPSRL0
	.cfi_def_cfa_register 7
	subq	$32, %rsp
	.cfi_def_cfa_offset 65616
	leaq	.LC3(%rip), %rsi
	movq	%fs:40, %rbx
	movq	%rbx, 65560(%rsp)
	movq	%rdi, %rbx
	call	fopen@PLT
	testq	%rax, %rax
	je	.L28
	movq	%rax, %r13
	xorl	%ebx, %ebx
	xorl	%ebp, %ebp
	jmp	.L23
	.p2align 4,,10
	.p2align 3
.L24:
	movq	%rax, %rdx
	leaq	16(%rsp), %rsi
	movq	%rsp, %rdi
	movq	%rbp, (%rsp)
	movq	%rbx, 8(%rsp)
	call	app
	movq	(%rsp), %rbp
	movq	8(%rsp), %rbx
.L23:
	movq	%r13, %rcx
	movl	$65536, %edx
	movl	$1, %esi
	leaq	16(%rsp), %rdi
	call	fread@PLT
	testq	%rax, %rax
	jne	.L24
	movq	%r13, %rdi
	call	fclose@PLT
	movq	%rbp, %rax
	movq	%rbx, %rdx
	movq	65560(%rsp), %rcx
	subq	%fs:40, %rcx
	jne	.L29
	addq	$65568, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 48
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%rbp
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r13
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	ret
.L28:
	.cfi_restore_state
	movq	%rbx, %rdi
	call	die
.L29:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE88:
	.size	readfile, .-readfile
	.p2align 4
	.type	blake2s, @function
blake2s:
.LFB79:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movl	%edx, %ecx
	shrl	$3, %ecx
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r12
	.cfi_offset 12, -24
	movq	%rdi, %r12
	pushq	%rbx
	andq	$-32, %rsp
	addq	$-128, %rsp
	.cfi_offset 3, -32
	vmovdqa	.LC4(%rip), %ymm0
	movq	%fs:40, %rax
	movq	%rax, 120(%rsp)
	xorl	%eax, %eax
	leaq	48(%rsp), %rdi
	vmovdqa	%ymm0, (%rsp)
	vpxor	%xmm0, %xmm0, %xmm0
	vmovdqu	%ymm0, 48(%rsp)
	vmovdqu	%ymm0, 80(%rsp)
	rep movsq
	testb	$4, %dl
	je	.L31
	movl	(%rsi), %eax
	movl	%eax, (%rdi)
	movl	$4, %eax
.L31:
	testb	$2, %dl
	je	.L32
	movzwl	(%rsi,%rax), %ecx
	movw	%cx, (%rdi,%rax)
	addq	$2, %rax
.L32:
	testb	$1, %dl
	je	.L33
	movzbl	(%rsi,%rax), %ecx
	movb	%cl, (%rdi,%rax)
.L33:
	movq	%rsp, %rdi
	movl	$1, %ecx
	leaq	48(%rsp), %rsi
	vzeroupper
	call	compress
	movq	%rsp, %r8
	xorl	%edi, %edi
	.p2align 4
	.p2align 3
.L34:
	movl	(%r8), %esi
	leaq	(%r12,%rdi), %rdx
	xorl	%eax, %eax
.L35:
	shrx	%eax, %esi, %ecx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$32, %eax
	jne	.L35
	addq	$4, %rdi
	addq	$4, %r8
	cmpq	$32, %rdi
	jne	.L34
	movq	120(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L50
	leaq	-16(%rbp), %rsp
	popq	%rbx
	popq	%r12
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L50:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE79:
	.size	blake2s, .-blake2s
	.section	.rodata.str1.1
.LC6:
	.string	"ready"
.LC7:
	.string	"go"
.LC8:
	.string	"no go"
	.text
	.p2align 4
	.type	handshake, @function
handshake:
.LFB99:
	.cfi_startproc
	subq	$88, %rsp
	.cfi_def_cfa_offset 96
	movq	%fs:40, %rdi
	movq	%rdi, 72(%rsp)
	leaq	.LC6(%rip), %rdi
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
	movq	stdin(%rip), %rdx
	movq	%rsp, %rdi
	movl	$64, %esi
	call	fgets@PLT
	testq	%rax, %rax
	je	.L52
	cmpw	$28519, (%rsp)
	je	.L63
.L52:
	leaq	.LC8(%rip), %rdi
	call	die
.L63:
	movq	72(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L64
	addq	$88, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 8
	ret
.L64:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE99:
	.size	handshake, .-handshake
	.section	.rodata.str1.1
.LC9:
	.string	"RF_ORACLE"
.LC10:
	.string	"RF_ORACLE unset"
	.section	.rodata.str1.8,"aMS",@progbits,1
	.align 8
.LC11:
	.string	"cannot connect to the oracle service"
	.section	.rodata.str1.1
.LC12:
	.string	"SIGN write"
.LC13:
	.string	"SIGN read"
.LC14:
	.string	"SIGN refused"
	.text
	.p2align 4
	.type	signed_file, @function
signed_file:
.LFB97:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	pushq	%r13
	.cfi_def_cfa_offset 24
	.cfi_offset 13, -24
	pushq	%r12
	.cfi_def_cfa_offset 32
	.cfi_offset 12, -32
	pushq	%rbp
	.cfi_def_cfa_offset 40
	.cfi_offset 6, -40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset 3, -48
	subq	$4096, %rsp
	.cfi_def_cfa_offset 4144
	orq	$0, (%rsp)
	subq	$832, %rsp
	.cfi_def_cfa_offset 4976
	movl	svc(%rip), %eax
	movq	%fs:40, %r12
	movq	%r12, 4920(%rsp)
	movq	%rsi, %r12
	movq	%rdi, %r13
	testl	%eax, %eax
	js	.L66
.L72:
	leaq	128(%rsp), %rbp
	movl	svc(%rip), %edi
	movl	$16, %edx
	movq	$2, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	%rbp, %rsi
	call	write@PLT
	cmpq	$16, %rax
	jne	.L67
	xorl	%ebx, %ebx
	.p2align 4
	.p2align 3
.L68:
	movl	$16, %edx
	movl	svc(%rip), %edi
	leaq	0(%rbp,%rbx), %rsi
	subq	%rbx, %rdx
	movq	%rdx, %rcx
	call	__read_chk@PLT
	testq	%rax, %rax
	jle	.L77
	addq	%rax, %rbx
	cmpq	$15, %rbx
	jbe	.L68
	cmpb	$0, 128(%rsp)
	jne	.L74
	movq	%rbp, %rax
	leaq	120(%rsp), %rsi
	xorl	%edx, %edx
	.p2align 5
	.p2align 4
	.p2align 3
.L75:
	movzbl	15(%rax), %ecx
	salq	$8, %rdx
	subq	$1, %rax
	orq	%rcx, %rdx
	cmpq	%rsi, %rax
	jne	.L75
	cmpq	$4772, %rdx
	jne	.L74
	xorl	%ebx, %ebx
	leaq	144(%rsp), %r14
	movl	$4772, %ebp
	.p2align 4
	.p2align 3
.L76:
	movq	%rbp, %rdx
	movl	svc(%rip), %edi
	leaq	(%r14,%rbx), %rsi
	subq	%rbx, %rdx
	movq	%rdx, %rcx
	call	__read_chk@PLT
	testq	%rax, %rax
	jle	.L77
	addq	%rax, %rbx
	cmpq	$4771, %rbx
	jbe	.L76
	movq	%r12, %rsi
	movq	%rsp, %rdi
	movq	$0, (%rsp)
	movq	$0, 8(%rsp)
	call	app64
	movq	%r12, %rdx
	movq	%r13, %rsi
	movq	%rsp, %rdi
	call	app
	xorl	%esi, %esi
	movq	%rsp, %rdi
	call	app64
	movl	144(%rsp), %esi
	movq	%rsp, %rdi
	call	app64
	movl	$4768, %edx
	leaq	148(%rsp), %rsi
	movq	%rsp, %rdi
	call	app
	movq	(%rsp), %rax
	movq	8(%rsp), %rdx
	movq	4920(%rsp), %rcx
	subq	%fs:40, %rcx
	jne	.L84
	addq	$4928, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 48
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%rbp
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r13
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	ret
.L66:
	.cfi_restore_state
	leaq	.LC9(%rip), %rdi
	call	getenv@PLT
	movq	%rax, %rsi
	testq	%rax, %rax
	je	.L85
	xorl	%eax, %eax
	movl	$27, %ecx
	leaq	18(%rsp), %rdi
	movl	$107, %edx
	rep stosl
	leaq	18(%rsp), %rdi
	movw	$1, 16(%rsp)
	call	strncpy@PLT
	xorl	%edx, %edx
	movl	$1, %esi
	movl	$1, %edi
	call	socket@PLT
	movl	%eax, svc(%rip)
	testl	%eax, %eax
	js	.L71
	movl	$110, %edx
	leaq	16(%rsp), %rsi
	movl	%eax, %edi
	call	connect@PLT
	testl	%eax, %eax
	je	.L72
.L71:
	leaq	.LC11(%rip), %rdi
	call	die
.L77:
	leaq	.LC13(%rip), %rdi
	call	die
.L67:
	leaq	.LC12(%rip), %rdi
	call	die
.L84:
	call	__stack_chk_fail@PLT
.L74:
	leaq	.LC14(%rip), %rdi
	call	die
.L85:
	leaq	.LC10(%rip), %rdi
	call	die
	.cfi_endproc
.LFE97:
	.size	signed_file, .-signed_file
	.section	.rodata.str1.1
.LC15:
	.string	"%2x"
	.text
	.p2align 4
	.type	unhex.constprop.0, @function
unhex.constprop.0:
.LFB106:
	.cfi_startproc
	pushq	%r13
	.cfi_def_cfa_offset 16
	.cfi_offset 13, -16
	pushq	%r12
	.cfi_def_cfa_offset 24
	.cfi_offset 12, -24
	pushq	%rbp
	.cfi_def_cfa_offset 32
	.cfi_offset 6, -32
	movq	%rdi, %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 40
	.cfi_offset 3, -40
	subq	$24, %rsp
	.cfi_def_cfa_offset 64
	movq	%fs:40, %rbx
	movq	%rbx, 8(%rsp)
	movq	%rsi, %rbx
	leaq	64(%rbx), %r13
	.p2align 4
	.p2align 3
.L89:
	xorl	%eax, %eax
	leaq	4(%rsp), %rdx
	leaq	.LC15(%rip), %rsi
	movq	%rbx, %rdi
	call	__isoc23_sscanf@PLT
	cmpl	$1, %eax
	jne	.L93
	movl	4(%rsp), %eax
	addq	$2, %rbx
	addq	$1, %rbp
	movb	%al, -1(%rbp)
	cmpq	%r13, %rbx
	jne	.L89
	xorl	%eax, %eax
.L86:
	movq	8(%rsp), %rdx
	subq	%fs:40, %rdx
	jne	.L94
	addq	$24, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%rbp
	.cfi_def_cfa_offset 24
	popq	%r12
	.cfi_def_cfa_offset 16
	popq	%r13
	.cfi_def_cfa_offset 8
	ret
.L93:
	.cfi_restore_state
	movl	$-1, %eax
	jmp	.L86
.L94:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE106:
	.size	unhex.constprop.0, .-unhex.constprop.0
	.section	.rodata.str1.1
.LC16:
	.string	""
.LC17:
	.string	"\"n\":"
.LC18:
	.string	"\"start\":"
	.text
	.p2align 4
	.type	prove_chain_file, @function
prove_chain_file:
.LFB100:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	.cfi_offset 15, -24
	.cfi_offset 14, -32
	.cfi_offset 13, -40
	.cfi_offset 12, -48
	movq	%rdi, %r12
	pushq	%rbx
	andq	$-32, %rsp
	subq	$224, %rsp
	.cfi_offset 3, -56
	movq	%rsi, 24(%rsp)
	movq	%fs:40, %rax
	movq	%rax, 216(%rsp)
	xorl	%eax, %eax
	call	readfile
	leaq	32(%rsp), %rdi
	leaq	.LC16(%rip), %rsi
	movq	%rdx, 40(%rsp)
	movl	$1, %edx
	movq	%rax, 32(%rsp)
	call	app
	movq	32(%rsp), %r13
	leaq	.LC17(%rip), %rsi
	movq	%r13, %rdi
	call	strstr@PLT
	leaq	.LC18(%rip), %rsi
	movq	%r13, %rdi
	movq	%rax, %rbx
	call	strstr@PLT
	testq	%rbx, %rbx
	je	.L99
	testq	%rax, %rax
	je	.L99
	leaq	8(%rax), %rdi
	movl	$34, %esi
	call	strchr@PLT
	testq	%rax, %rax
	je	.L99
	leaq	1(%rax), %rsi
	leaq	64(%rsp), %rdi
	call	unhex.constprop.0
	testl	%eax, %eax
	jne	.L99
	leaq	4(%rbx), %rdi
	movl	$10, %edx
	xorl	%esi, %esi
	call	__isoc23_strtoull@PLT
	vmovdqa	64(%rsp), %ymm0
	leaq	160(%rsp), %r12
	movq	%rax, %rbx
	vmovdqa	%ymm0, 128(%rsp)
	testq	%rax, %rax
	je	.L101
	xorl	%r14d, %r14d
	leaq	160(%rsp), %r12
	.p2align 4
	.p2align 3
.L102:
	movb	$67, 160(%rsp)
	movl	$33, %edx
	movq	%r12, %rsi
	leaq	96(%rsp), %rdi
	vmovdqu	%ymm0, 161(%rsp)
	vmovdqa	%ymm0, 96(%rsp)
	vzeroupper
	call	blake2s
	addq	$1, %r14
	vmovdqa	96(%rsp), %ymm0
	cmpq	%r14, %rbx
	jne	.L102
.L101:
	movb	$76, 160(%rsp)
	leaq	193(%rsp), %rdx
	xorl	%eax, %eax
	vmovdqu	%ymm0, 161(%rsp)
	.p2align 5
	.p2align 4
	.p2align 3
.L103:
	shrx	%rax, %rbx, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L103
	movq	24(%rsp), %rdi
	movl	$41, %edx
	movq	%r12, %rsi
	vzeroupper
	call	blake2s
	xorl	%esi, %esi
	leaq	48(%rsp), %rdi
	movq	$0, 48(%rsp)
	movq	$0, 56(%rsp)
	call	app64
	movl	$32, %edx
	leaq	48(%rsp), %rdi
	leaq	128(%rsp), %rsi
	call	app
	movq	%rbx, %rsi
	leaq	48(%rsp), %rdi
	call	app64
	movq	48(%rsp), %r12
	movq	56(%rsp), %rdx
	movq	%r12, %rdi
	movq	%rdx, %rsi
	call	signed_file
	movq	%r12, %rdi
	movq	%rax, %r14
	movq	%rdx, %rbx
	call	free@PLT
	movq	%r13, %rdi
	call	free@PLT
	movq	%r14, %rax
	movq	%rbx, %rdx
	movq	216(%rsp), %rcx
	subq	%fs:40, %rcx
	jne	.L111
	leaq	-40(%rbp), %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L99:
	.cfi_restore_state
	movq	%r12, %rdi
	call	die
.L111:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE100:
	.size	prove_chain_file, .-prove_chain_file
	.section	.rodata.str1.1
.LC19:
	.string	"proof.bin"
.LC20:
	.string	"%s.tmp"
.LC21:
	.string	"wb"
	.text
	.p2align 4
	.type	writefile.constprop.0, @function
writefile.constprop.0:
.LFB107:
	.cfi_startproc
	pushq	%r13
	.cfi_def_cfa_offset 16
	.cfi_offset 13, -16
	leaq	.LC19(%rip), %r9
	movq	%rdi, %r13
	leaq	.LC20(%rip), %r8
	pushq	%r12
	.cfi_def_cfa_offset 24
	.cfi_offset 12, -24
	movl	$512, %ecx
	movq	%rsi, %r12
	movl	$2, %edx
	pushq	%rbp
	.cfi_def_cfa_offset 32
	.cfi_offset 6, -32
	movl	$512, %esi
	pushq	%rbx
	.cfi_def_cfa_offset 40
	.cfi_offset 3, -40
	subq	$536, %rsp
	.cfi_def_cfa_offset 576
	movq	%fs:40, %rax
	movq	%rax, 520(%rsp)
	xorl	%eax, %eax
	movq	%rsp, %rdi
	call	__snprintf_chk@PLT
	leaq	.LC21(%rip), %rsi
	movq	%rsp, %rdi
	call	fopen@PLT
	testq	%rax, %rax
	je	.L114
	movq	%rax, %rcx
	movq	%r12, %rdx
	movl	$1, %esi
	movq	%r13, %rdi
	movq	%rax, %rbp
	call	fwrite@PLT
	cmpq	%rax, %r12
	jne	.L114
	movq	%rbp, %rdi
	call	fclose@PLT
	testl	%eax, %eax
	jne	.L114
	leaq	.LC19(%rip), %rsi
	movq	%rsp, %rdi
	call	rename@PLT
	testl	%eax, %eax
	jne	.L114
	movq	520(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L121
	addq	$536, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%rbp
	.cfi_def_cfa_offset 24
	popq	%r12
	.cfi_def_cfa_offset 16
	popq	%r13
	.cfi_def_cfa_offset 8
	ret
.L114:
	.cfi_restore_state
	leaq	.LC19(%rip), %rdi
	call	die
.L121:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE107:
	.size	writefile.constprop.0, .-writefile.constprop.0
	.section	.rodata.str1.1
.LC22:
	.string	"malformed child file"
	.section	.rodata.str1.8
	.align 8
.LC23:
	.string	"trailing bytes in a child file"
	.text
	.p2align 4
	.type	app_signed_words, @function
app_signed_words:
.LFB95:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	andq	$-32, %rsp
	subq	$96, %rsp
	.cfi_offset 15, -24
	.cfi_offset 14, -32
	.cfi_offset 13, -40
	.cfi_offset 12, -48
	.cfi_offset 3, -56
	movq	%fs:40, %rax
	movq	%rax, 88(%rsp)
	xorl	%eax, %eax
	cmpq	$7, %rdx
	jbe	.L125
	movq	%rdi, %rbx
	movq	%rsi, %r12
	movq	%rdx, %r13
	xorl	%r15d, %r15d
	leaq	7(%rsi), %rax
	leaq	-1(%rsi), %rcx
	.p2align 5
	.p2align 4
	.p2align 3
.L124:
	movzbl	(%rax), %edx
	salq	$8, %r15
	subq	$1, %rax
	orq	%rdx, %r15
	cmpq	%rcx, %rax
	jne	.L124
	leaq	-8(%r13), %r8
	cmpq	%r15, %r8
	jb	.L125
	leaq	64(%rsp), %rdx
	xorl	%eax, %eax
	movq	%rdx, 56(%rsp)
	.p2align 5
	.p2align 4
	.p2align 3
.L126:
	shrx	%rax, %r15, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L126
	movq	56(%rsp), %rsi
	movl	$8, %edx
	movq	%rbx, %rdi
	movq	%r8, 48(%rsp)
	call	app
	movq	%r15, %rdx
	leaq	8(%r12), %rsi
	movq	%rbx, %rdi
	call	app
	movq	%r15, %rdx
	leaq	ZERO8(%rip), %rsi
	movq	%rbx, %rdi
	negq	%rdx
	andl	$7, %edx
	call	app
	movq	48(%rsp), %r8
	subq	%r15, %r8
	cmpq	$7, %r8
	jbe	.L125
	leaq	-8(%r12), %rdi
	leaq	(%r15,%r12), %rax
	movq	$0, 32(%rsp)
	movq	%rdi, 24(%rsp)
	leaq	(%r15,%rdi), %rsi
	.p2align 5
	.p2align 4
	.p2align 3
.L127:
	movq	32(%rsp), %rdx
	movzbl	15(%rax), %ecx
	subq	$1, %rax
	salq	$8, %rdx
	orq	%rdx, %rcx
	movq	%rcx, 32(%rsp)
	cmpq	%rax, %rsi
	jne	.L127
	movq	%rcx, %r14
	movq	%rcx, %rsi
	movq	%rbx, %rdi
	addq	$16, %r15
	call	app64
	testq	%r14, %r14
	je	.L128
	xorl	%r14d, %r14d
	.p2align 4
	.p2align 3
.L131:
	movq	%r13, %rax
	subq	%r15, %rax
	cmpq	$7, %rax
	jbe	.L125
	movq	24(%rsp), %rax
	leaq	(%r15,%r12), %rdx
	leaq	(%r15,%rax), %rsi
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L129:
	movzbl	7(%rdx), %ecx
	salq	$8, %rax
	subq	$1, %rdx
	orq	%rcx, %rax
	cmpq	%rdx, %rsi
	jne	.L129
	addq	$8, %r15
	movq	%r13, %rdx
	subq	%r15, %rdx
	cmpq	%rax, %rdx
	jb	.L125
	leaq	(%r12,%r15), %rdi
	movq	56(%rsp), %rcx
	xorl	%edx, %edx
	movq	%rdi, 48(%rsp)
	.p2align 5
	.p2align 4
	.p2align 3
.L130:
	shrx	%rdx, %rax, %rsi
	addl	$8, %edx
	movb	%sil, (%rcx)
	addq	$1, %rcx
	cmpl	$64, %edx
	jne	.L130
	movq	56(%rsp), %rsi
	movl	$8, %edx
	movq	%rbx, %rdi
	movq	%rax, 40(%rsp)
	call	app
	movq	40(%rsp), %rdx
	movq	48(%rsp), %rsi
	movq	%rbx, %rdi
	call	app
	movq	40(%rsp), %rax
	leaq	ZERO8(%rip), %rsi
	movq	%rbx, %rdi
	movq	%rax, %rdx
	movq	%rax, 48(%rsp)
	negq	%rdx
	andl	$7, %edx
	call	app
	addq	48(%rsp), %r15
	movq	%r13, %rax
	subq	%r15, %rax
	cmpq	$31, %rax
	jbe	.L125
	leaq	(%r12,%r15), %rsi
	movl	$32, %edx
	movq	%rbx, %rdi
	addq	$32, %r15
	call	app
	addq	$1, %r14
	cmpq	32(%rsp), %r14
	jne	.L131
.L128:
	movq	%r13, %rax
	subq	%r15, %rax
	cmpq	$4775, %rax
	jbe	.L125
	leaq	(%r12,%r15), %rsi
	movl	$4776, %edx
	movq	%rbx, %rdi
	addq	$4776, %r15
	call	app
	cmpq	%r15, %r13
	jne	.L145
	movq	88(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L146
	leaq	-40(%rbp), %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L125:
	.cfi_restore_state
	leaq	.LC22(%rip), %rdi
	call	die
.L146:
	call	__stack_chk_fail@PLT
.L145:
	leaq	.LC23(%rip), %rdi
	call	die
	.cfi_endproc
.LFE95:
	.size	app_signed_words, .-app_signed_words
	.p2align 4
	.type	ws_node, @function
ws_node:
.LFB96:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	movq	%rdi, %r15
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	movq	%rsi, %r14
	movl	$1, %esi
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	movq	%rdx, %r13
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	movq	%rcx, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$56, %rsp
	.cfi_def_cfa_offset 112
	movq	%r8, 8(%rsp)
	leaq	16(%rsp), %rdi
	movq	%fs:40, %rbp
	movq	%rbp, 40(%rsp)
	movq	%r9, %rbp
	movq	$0, 16(%rsp)
	movq	$0, 24(%rsp)
	call	app64
	movl	$32, %edx
	movq	%r15, %rsi
	leaq	16(%rsp), %rdi
	call	app
	movl	$32, %edx
	movq	%r14, %rsi
	leaq	16(%rsp), %rdi
	call	app
	movq	%r13, %rsi
	movq	%r12, %rdx
	leaq	16(%rsp), %rdi
	call	app_signed_words
	movq	8(%rsp), %rsi
	leaq	16(%rsp), %rdi
	movq	%rbp, %rdx
	call	app_signed_words
	movq	16(%rsp), %rax
	movq	24(%rsp), %rdx
	movq	40(%rsp), %rcx
	subq	%fs:40, %rcx
	jne	.L150
	addq	$56, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
.L150:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE96:
	.size	ws_node, .-ws_node
	.section	.rodata.str1.8
	.align 8
.LC24:
	.string	"usage: prover setup|first|step DIR"
	.section	.rodata.str1.1
.LC25:
	.string	"cannot enter DIR"
.LC26:
	.string	"setup"
.LC27:
	.string	"first"
.LC28:
	.string	"chainA.json"
.LC29:
	.string	"chainB.json"
.LC30:
	.string	"done"
.LC31:
	.string	"step"
.LC32:
	.string	"prev.stmt"
.LC33:
	.string	"prev.bin"
.LC34:
	.string	"chain.json"
.LC35:
	.string	"unknown mode"
	.section	.text.startup,"ax",@progbits
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB103:
	.cfi_startproc
	endbr64
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
	subq	$112, %rsp
	.cfi_def_cfa_offset 144
	movq	%fs:40, %rax
	movq	%rax, 104(%rsp)
	xorl	%eax, %eax
	cmpl	$3, %edi
	jne	.L165
	movq	16(%rsi), %rdi
	movq	%rsi, %rbx
	call	chdir@PLT
	testl	%eax, %eax
	jne	.L166
	movq	8(%rbx), %rbx
	leaq	.LC26(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L154
	leaq	.LC27(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L167
	leaq	.LC31(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	jne	.L156
	call	handshake
	leaq	.LC32(%rip), %rdi
	call	readfile
	leaq	16(%rsp), %rdi
	leaq	.LC16(%rip), %rsi
	movq	%rdx, 24(%rsp)
	movl	$1, %edx
	movq	%rax, 16(%rsp)
	call	app
	cmpq	$64, 24(%rsp)
	jbe	.L158
	movq	16(%rsp), %rdx
	leaq	32(%rsp), %rdi
	movq	%rdx, %rsi
	movq	%rdx, 8(%rsp)
	call	unhex.constprop.0
	testl	%eax, %eax
	jne	.L158
	movq	8(%rsp), %rdi
	call	free@PLT
	leaq	.LC33(%rip), %rdi
	call	readfile
	leaq	64(%rsp), %rsi
	leaq	.LC34(%rip), %rdi
	movq	%rsi, 8(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
.L164:
	call	prove_chain_file
	movq	8(%rsp), %rsi
	movq	%r15, %rcx
	leaq	32(%rsp), %rdi
	movq	%rdx, %r9
	movq	%rax, %r8
	movq	%r14, %rdx
	call	ws_node
	movq	%rax, %rdi
	movq	%rdx, %rsi
	call	signed_file
	movq	%rax, %rdi
	movq	%rdx, %rsi
	call	writefile.constprop.0
	leaq	.LC30(%rip), %rdi
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
.L154:
	movq	104(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L168
	addq	$112, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 32
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
.L167:
	.cfi_restore_state
	call	handshake
	leaq	32(%rsp), %rsi
	leaq	.LC28(%rip), %rdi
	call	prove_chain_file
	leaq	64(%rsp), %rsi
	leaq	.LC29(%rip), %rdi
	movq	%rsi, 8(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	jmp	.L164
.L158:
	leaq	.LC32(%rip), %rdi
	call	die
.L166:
	leaq	.LC25(%rip), %rdi
	call	die
.L165:
	leaq	.LC24(%rip), %rdi
	call	die
.L168:
	call	__stack_chk_fail@PLT
.L156:
	leaq	.LC35(%rip), %rdi
	call	die
	.cfi_endproc
.LFE103:
	.size	main, .-main
	.section	.rodata
	.align 8
	.type	ZERO8, @object
	.size	ZERO8, 8
ZERO8:
	.zero	8
	.data
	.align 4
	.type	svc, @object
	.size	svc, 4
svc:
	.long	-1
	.section	.rodata
	.align 32
	.type	SIGMA, @object
	.size	SIGMA, 160
SIGMA:
	.byte	0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
	.byte	14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3
	.string	"\013\b\f"
	.byte	5,2,15,13,10,14,3,6,7,1,9,4
	.byte	7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8
	.string	"\t"
	.byte	5,7,2,4,10,15,14,1,11,12,6,8,3,13
	.byte	2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9
	.byte	12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11
	.byte	13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10
	.byte	6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5
	.byte	10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0
	.section	.rodata.cst32,"aM",@progbits,32
	.align 32
.LC4:
	.long	1795745351
	.long	-1150833019
	.long	1013904242
	.long	-1521486534
	.long	1359893119
	.long	-1694144372
	.long	528734635
	.long	1541459225
	.ident	"GCC: (Ubuntu 15.2.0-16ubuntu1) 15.2.0"
	.section	.note.GNU-stack,"",@progbits
	.section	.note.gnu.property,"a"
	.align 8
	.long	1f - 0f
	.long	4f - 1f
	.long	5
0:
	.string	"GNU"
1:
	.align 8
	.long	0xc0000002
	.long	3f - 2f
2:
	.long	0x3
3:
	.align 8
4:
